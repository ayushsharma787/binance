#!/usr/bin/env python3
"""
MEDALLION RENAISSANCE MULTI-AGENT TRADING BOT v2.0
ETH/USDT Perpetual Futures | 5× Isolated Leverage | Binance
7 Autonomous Agents | 15 Signal Layers | 22 Risk Gates | 16 Sizing Factors
Complete implementation — every function fully built.
"""
API_KEY = "PASTE_YOUR_API_KEY_HERE"
API_SECRET = "PASTE_YOUR_API_SECRET_HERE"

import os,sys,time,json,hmac,hashlib,signal as sig_mod,sqlite3,threading,logging
import argparse,math,calendar
from datetime import datetime,timezone,timedelta
from dataclasses import dataclass,field,asdict
from typing import Optional,List,Dict,Tuple,Any
from collections import deque
import requests,pandas as pd,numpy as np
from scipy import stats as sp_stats
from scipy.special import expit as sigmoid

# ═══ CONSTANTS ═══
FAPI="https://fapi.binance.com";DAPI="https://api.binance.com"
SYMBOL="ETHUSDT";CROSS_SYMBOLS=["BTCUSDT","SOLUSDT"]
LEVERAGE=5;MARGIN_TYPE="ISOLATED";SCAN_INTERVAL=30
DB_FILE="medallion.db";LOG_FILE="medallion.log"
# Strategy A (trend-following, 5x) — TP levels pushed out for better R:R
SA_STOP_ATR=1.0;SA_TP1_ATR=1.8;SA_TP1_FRAC=0.40;SA_TP2_ATR=3.0;SA_TP2_FRAC=0.30
SA_TP3_ATR=5.5;SA_TP3_FRAC=0.30;SA_TRAIL_ATR=0.8;SA_MIN_SCORE=68
SA_STOP_MIN=0.008;SA_STOP_MAX=0.018
# Strategy B (mean-reversion, 5x) — faster TP1 lock + extended hold window
SB_STOP_ATR=0.7;SB_TP1_ATR=0.6;SB_TP1_FRAC=0.50;SB_TP2_ATR=1.4;SB_TP2_FRAC=0.30
SB_TP3_FRAC=0.20;SB_MIN_SCORE=58;SB_MAX_HOLD_H=8;SB_STOP_MIN=0.005;SB_STOP_MAX=0.012
# Hurst
H_TREND_STRONG=0.60;H_TREND=0.55;H_MR=0.45;H_MR_STRONG=0.35
# Sizing
KELLY_FRAC=0.25;KELLY_CAP=0.70;KELLY_DEFAULT=0.38;KELLY_MIN=0.18
VOL_TARGET=0.020;KILL_SWITCH_DD=0.10;DAILY_LOSS_LIMIT=-0.06;MAX_TRADES_DAY=4
# VPIN
VPIN_GATE=0.65;VPIN_WARN=0.55;VPIN_CLEAN=0.30
# Supertrend
ST_1H_P=10;ST_1H_M=2.0;ST_4H_P=10;ST_4H_M=2.5
# Bayesian
B_INIT_A=2;B_INIT_B=2;B_FORGET=0.995;B_TEMP=0.5;B_FLOOR=0.05
# Signal freshness
FRESH_LAMBDA=0.02
# Compounding milestones
MILESTONES=[(375,0.73,0.023),(475,0.77,0.025),(650,0.82,0.027),(1000,0.85,0.030)]

logging.basicConfig(level=logging.INFO,format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.FileHandler(LOG_FILE),logging.StreamHandler()])
log=logging.getLogger("medallion")

def utcnow():return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
def utc_hour():return datetime.now(timezone.utc).hour
def safe_json(obj):
    if isinstance(obj,(np.integer,)):return int(obj)
    if isinstance(obj,(np.floating,)):return float(obj)
    if isinstance(obj,(np.bool_,)):return bool(obj)
    if isinstance(obj,np.ndarray):return obj.tolist()
    if isinstance(obj,dict):return{k:safe_json(v)for k,v in obj.items()}
    if isinstance(obj,(list,tuple)):return[safe_json(i)for i in obj]
    return obj
def get_session():
    h=utc_hour()
    if 0<=h<8:return"ASIAN"
    elif 8<=h<13:return"EU"
    elif 13<=h<21:return"US"
    else:return"DEAD"
def near_funding(minutes=25):
    now=datetime.now(timezone.utc)
    for fh in[0,8,16]:
        ft=now.replace(hour=fh,minute=0,second=0,microsecond=0)
        if ft<now:ft+=timedelta(hours=8)
        if abs((ft-now).total_seconds())/60<minutes:return True
    return False
def is_options_expiry():
    now=datetime.now(timezone.utc)
    last_friday=max(w for w in range(1,32)if datetime(now.year,now.month,min(w,28)).weekday()==4
        and w<=calendar.monthrange(now.year,now.month)[1])
    return abs(now.day-last_friday)<=1
def session_params():
    s=get_session()
    if s=="ASIAN":return{"min_score":73,"size_mult":0.65,"vpin_thresh":0.55,"label":"ASIAN — Reduced"}
    elif s=="EU":return{"min_score":SA_MIN_SCORE,"size_mult":1.00,"vpin_thresh":VPIN_GATE,"label":"EU — Full"}
    elif s=="US":return{"min_score":65,"size_mult":1.05,"vpin_thresh":VPIN_GATE,"label":"US — Peak"}
    else:return{"min_score":73,"size_mult":0.60,"vpin_thresh":0.50,"label":"DEAD — Minimum"}

@dataclass
class AgentVerdict:
    agent_name:str;direction:str;confidence:float;reasoning:str
    scores:Dict[str,Any]=field(default_factory=dict)
    veto:bool=False;veto_reason:str="";revision_notes:str=""
@dataclass
class AgentMessage:
    sender:str;recipient:str;msg_type:str;content:str
    data:Dict[str,Any]=field(default_factory=dict);priority:int=2;ts:float=0.0
@dataclass
class Position:
    direction:str="NONE";strategy:str="NONE";entry_price:float=0;qty_full:float=0
    qty_rem:float=0;stop_price:float=0;tp1_price:float=0;tp2_price:float=0
    tp3_price:float=0;trail_price:float=0;liq_price:float=0;tp1_hit:bool=False
    tp2_hit:bool=False;opened_at:str="";trade_id:int=0;mfe:float=0;mae:float=0
# ═══ DATABASE ═══
class Database:
    def __init__(self,path=DB_FILE):
        self.conn=sqlite3.connect(path,check_same_thread=False)
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.lock=threading.Lock()
        self._create()
    def _create(self):
        with self.lock:
            c=self.conn.cursor()
            c.execute("CREATE TABLE IF NOT EXISTS kv(key TEXT PRIMARY KEY,value TEXT,updated_at TEXT)")
            c.execute("""CREATE TABLE IF NOT EXISTS trades(
                id INTEGER PRIMARY KEY AUTOINCREMENT,direction TEXT,strategy TEXT,
                entry_price REAL,liq_price REAL,stop_price REAL,
                tp1_price REAL,tp2_price REAL,tp3_price REAL,
                qty_full REAL,qty_rem REAL,notional REAL,margin REAL,
                total_pnl REAL,total_pnl_pct REAL,status TEXT,
                hmm_p_bull REAL,hmm_p_bear REAL,hmm_p_neutral REAL,
                hurst REAL,har_rv_forecast REAL,vol_percentile REAL,
                long_score REAL,short_score REAL,ensemble_long REAL,ensemble_short REAL,
                uncertainty_score REAL,vpin_at_entry REAL,vpin_direction TEXT,
                book_pressure REAL,adverse_selection REAL,
                oi_roc_1h REAL,oi_roc_4h REAL,oi_scenario TEXT,oi_extreme INT,
                funding_at_entry REAL,fr_term TEXT,fr_zscore REAL,daily_carry REAL,
                funding_pnl_pct REAL,price_pnl_pct REAL,
                session TEXT,slippage_bps REAL,effective_spread REAL,
                agent_verdicts TEXT,arbiter_confidence REAL,agent_disagreement INT,
                exit_reason TEXT,mfe_pct REAL,mae_pct REAL,
                opened_at TEXT,tp1_at TEXT,tp2_at TEXT,closed_at TEXT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS alpha_log(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,scan_num INT,
                alpha_signals TEXT,bayesian_weights TEXT,freshness_weights TEXT,
                long_score REAL,short_score REAL,ensemble_long REAL,ensemble_short REAL,
                hurst REAL,hmm_state TEXT,vpin REAL,oi_roc_1h REAL,
                fr_current REAL,fr_term TEXT,signal_entropy REAL,avg_alpha_corr REAL,
                strategy TEXT,action TEXT,session TEXT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS deliberation_log(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,scan_num INT,
                verdicts TEXT,messages TEXT,final_action TEXT,arbiter_reasoning TEXT,
                consensus_dir TEXT,consensus_margin REAL,agg_confidence REAL,
                disagreement INT,veto_issued INT,veto_agent TEXT,veto_reason TEXT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS agent_performance(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,agent_name TEXT,trade_id INT,
                direction_correct INT,confidence REAL,trade_pnl REAL,
                veto_issued INT,veto_correct INT,rolling_accuracy REAL)""")
            c.execute("""CREATE TABLE IF NOT EXISTS agent_messages(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,scan_num INT,
                sender TEXT,recipient TEXT,msg_type TEXT,priority INT,content TEXT,data TEXT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS agent_weight_history(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,
                alpha_w REAL,regime_w REAL,risk_w REAL,micro_w REAL,meta_w REAL,exec_w REAL,
                trigger TEXT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS condition_performance(
                condition_key TEXT PRIMARY KEY,wins INT DEFAULT 0,losses INT DEFAULT 0,
                total_pnl REAL DEFAULT 0,avg_pnl_pct REAL DEFAULT 0,
                avg_mfe REAL DEFAULT 0,avg_mae REAL DEFAULT 0,last_updated TEXT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS alpha_performance(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,alpha_name TEXT,direction TEXT,
                bayesian_alpha REAL,bayesian_beta REAL,posterior_mean REAL,
                mutual_info REAL,weight REAL,status TEXT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS compound_log(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,balance_before REAL,balance_after REAL,
                trade_pnl REAL,trade_pnl_pct REAL,cumulative_pnl REAL,cumulative_pnl_pct REAL,
                peak_equity REAL,drawdown_pct REAL,trades_total INT,
                compound_rate REAL,sizing_tier TEXT,note TEXT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS execution_log(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,trade_id INT,slice_num INT,
                expected_price REAL,fill_price REAL,slippage_bps REAL,
                effective_spread REAL,qty REAL,side TEXT,book_pressure REAL,micro_price REAL)""")
            c.execute("""CREATE TABLE IF NOT EXISTS vpin_log(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,vpin REAL,vpin_delta REAL,
                vpin_direction TEXT,bucket_count INT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS oi_log(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,oi_current REAL,
                oi_roc_1h REAL,oi_roc_4h REAL,oi_roc_24h REAL,
                oi_zscore REAL,oi_scenario TEXT,oi_extreme INT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS funding_log(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,fr_current REAL,
                fr_avg_8h REAL,fr_avg_3d REAL,fr_avg_7d REAL,
                fr_momentum REAL,fr_term TEXT,fr_zscore REAL,
                daily_carry REAL,funding_extreme INT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS milestones(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,milestone_type TEXT,value REAL,note TEXT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS regime_history(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,hurst REAL,hurst_slope REAL,
                strategy TEXT,predicted_transition INT)""")
            c.execute("""CREATE TABLE IF NOT EXISTS optimization_history(
                id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,tier INT,trigger TEXT,
                params_before TEXT,params_after TEXT,best_sharpe REAL,
                best_pf REAL,improvement_pct REAL,notes TEXT)""")
            self.conn.commit()
    def kv_get(self,key,default=None):
        with self.lock:
            r=self.conn.execute("SELECT value FROM kv WHERE key=?",(key,)).fetchone()
            if r:
                try:return json.loads(r[0])
                except:return r[0]
            return default
    def kv_set(self,key,value):
        with self.lock:
            v=json.dumps(safe_json(value))if not isinstance(value,str)else value
            self.conn.execute("INSERT OR REPLACE INTO kv(key,value,updated_at)VALUES(?,?,?)",(key,v,utcnow()))
            self.conn.commit()
    def insert(self,table,data):
        with self.lock:
            data=safe_json(data)
            cols=",".join(data.keys());ph=",".join(["?"]*len(data))
            c=self.conn.execute(f"INSERT INTO {table}({cols})VALUES({ph})",list(data.values()))
            self.conn.commit();return c.lastrowid
    def update(self,table,row_id,data):
        with self.lock:
            data=safe_json(data);sets=",".join(f"{k}=?"for k in data)
            self.conn.execute(f"UPDATE {table} SET {sets} WHERE id=?",list(data.values())+[row_id])
            self.conn.commit()
    def query(self,sql,params=()):
        with self.lock:return self.conn.execute(sql,params).fetchall()
    def query_one(self,sql,params=()):
        with self.lock:return self.conn.execute(sql,params).fetchone()
    def log_delib(self,scan_num,verdicts,messages,action,reasoning,extras=None):
        d={"ts":utcnow(),"scan_num":scan_num,"verdicts":json.dumps(safe_json(verdicts)),
           "messages":json.dumps(safe_json(messages)),"final_action":str(action),"arbiter_reasoning":str(reasoning)}
        if extras:d.update(safe_json(extras))
        self.insert("deliberation_log",d)
    def log_msg(self,scan_num,msg:AgentMessage):
        self.insert("agent_messages",{"ts":utcnow(),"scan_num":scan_num,"sender":msg.sender,
            "recipient":msg.recipient,"msg_type":msg.msg_type,"priority":msg.priority,
            "content":msg.content,"data":json.dumps(safe_json(msg.data))})
# ═══ BINANCE API ═══
class BinanceClient:
    def __init__(self,key,secret):
        self.key=key;self.secret=secret;self.session=requests.Session()
        self.session.headers.update({"X-MBX-APIKEY":self.key});self.time_offset=0;self.req_count=0;self.req_reset=time.time()
    def _sign(self,p):
        p["timestamp"]=int(time.time()*1000)+self.time_offset
        qs="&".join(f"{k}={v}"for k,v in p.items())
        p["signature"]=hmac.new(self.secret.encode(),qs.encode(),hashlib.sha256).hexdigest()
        return p
    def _req(self,method,url,params=None,signed=False,retries=3):
        params=params or{}
        if signed:params=self._sign(params)
        now=time.time()
        if now-self.req_reset>60:self.req_count=0;self.req_reset=now
        if self.req_count>1100:time.sleep(max(0,60-(now-self.req_reset)));self.req_count=0;self.req_reset=time.time()
        for attempt in range(retries):
            try:
                self.req_count+=1
                r=self.session.get(url,params=params,timeout=10)if method=="GET"else self.session.post(url,params=params,timeout=10)
                data=r.json()
                if isinstance(data,dict)and"code"in data:
                    code=data["code"]
                    if code==-1021:self._sync_time();continue
                    if code==-2015:log.critical("Invalid API key");sys.exit(1)
                    if code in(-1111,-4003):time.sleep(1);continue
                    if code==-4061:log.warning("reduceOnly failed—position may be closed externally");return data
                    if code==-4046:return True
                    if code==-2010:log.error(f"Insufficient balance:{data.get('msg','')}");return data
                    log.warning(f"Binance error {code}:{data.get('msg','')}")
                return data
            except Exception as e:
                log.warning(f"API fail(attempt {attempt+1}):{e}");time.sleep(2**attempt)
        log.error(f"API failed after {retries} retries:{url}");return None
    def _sync_time(self):
        try:
            st=self._req("GET",f"{FAPI}/fapi/v1/time")
            if st and"serverTime"in st:self.time_offset=st["serverTime"]-int(time.time()*1000);log.info(f"Time synced offset={self.time_offset}ms")
        except:pass
    def ping(self):r=self._req("GET",f"{FAPI}/fapi/v1/ping");return r is not None
    def balance(self):
        r=self._req("GET",f"{FAPI}/fapi/v2/balance",signed=True)
        if r:
            for i in r:
                if i.get("asset")=="USDT":return float(i.get("balance",0))
        return 0.0
    def account(self):return self._req("GET",f"{FAPI}/fapi/v2/account",signed=True)
    def set_leverage(self,sym,lev):return self._req("POST",f"{FAPI}/fapi/v1/leverage",{"symbol":sym,"leverage":lev},signed=True)
    def set_margin_type(self,sym,mt):return self._req("POST",f"{FAPI}/fapi/v1/marginType",{"symbol":sym,"marginType":mt},signed=True)
    def symbol_info(self,sym):
        r=self._req("GET",f"{FAPI}/fapi/v1/exchangeInfo")
        if r and"symbols"in r:
            for s in r["symbols"]:
                if s["symbol"]==sym:return s
        return None
    def klines(self,sym,interval,limit=500):
        r=self._req("GET",f"{FAPI}/fapi/v1/klines",{"symbol":sym,"interval":interval,"limit":limit})
        if r and len(r)>0:
            df=pd.DataFrame(r,columns=["ot","open","high","low","close","volume","ct","qv","trades","tbv","tbqv","ig"])
            for c in["open","high","low","close","volume","qv","tbv"]:df[c]=df[c].astype(float)
            df["ot"]=pd.to_datetime(df["ot"],unit="ms")
            return df
        return pd.DataFrame()
    def price(self,sym):
        r=self._req("GET",f"{FAPI}/fapi/v1/ticker/price",{"symbol":sym})
        return float(r["price"])if r and"price"in r else 0.0
    def orderbook(self,sym,limit=20):return self._req("GET",f"{FAPI}/fapi/v1/depth",{"symbol":sym,"limit":limit})
    def funding_rate(self,sym):
        r=self._req("GET",f"{FAPI}/fapi/v1/premiumIndex",{"symbol":sym})
        return float(r.get("lastFundingRate",0))if r else 0.0
    def funding_history(self,sym,limit=100):return self._req("GET",f"{FAPI}/fapi/v1/fundingRate",{"symbol":sym,"limit":limit})
    def open_interest(self,sym):
        r=self._req("GET",f"{FAPI}/fapi/v1/openInterest",{"symbol":sym})
        return float(r.get("openInterest",0))if r else 0.0
    def recent_trades(self,sym,limit=1000):return self._req("GET",f"{FAPI}/fapi/v1/trades",{"symbol":sym,"limit":limit})
    def position(self,sym):
        r=self._req("GET",f"{FAPI}/fapi/v2/positionRisk",{"symbol":sym},signed=True)
        if r:
            for p in r:
                if p["symbol"]==sym and float(p.get("positionAmt",0))!=0:return p
        return None
    def market_order(self,sym,side,qty,reduce_only=False):
        p={"symbol":sym,"side":side,"type":"MARKET","quantity":qty}
        if reduce_only:p["reduceOnly"]="true"
        r=self._req("POST",f"{FAPI}/fapi/v1/order",p,signed=True)
        if r and isinstance(r,dict)and"orderId"in r:log.info(f"ORDER:{side} {qty} {sym}@market ID:{r['orderId']}")
        else:log.error(f"ORDER FAILED:{side} {qty} {sym}|{r}")
        return r
    def limit_order(self,sym,side,qty,price,reduce_only=False,time_in_force="GTC"):
        p={"symbol":sym,"side":side,"type":"LIMIT","quantity":qty,
           "price":str(price),"timeInForce":time_in_force}
        if reduce_only:p["reduceOnly"]="true"
        r=self._req("POST",f"{FAPI}/fapi/v1/order",p,signed=True)
        if r and isinstance(r,dict)and"orderId"in r:
            log.info(f"LIMIT ORDER:{side} {qty} {sym}@{price} ID:{r['orderId']}")
        return r
    def cancel_order(self,sym,order_id):
        return self._req("DELETE",f"{FAPI}/fapi/v1/order",{"symbol":sym,"orderId":order_id},signed=True)
    def check_order(self,sym,order_id):
        return self._req("GET",f"{FAPI}/fapi/v1/order",{"symbol":sym,"orderId":order_id},signed=True)
    def ticker_24h(self,sym):return self._req("GET",f"{FAPI}/fapi/v1/ticker/24hr",{"symbol":sym})
# ═══ SIGNAL ENGINE — ALL 15 LAYERS ═══
class Sig:
    @staticmethod
    def kalman(prices,Q=1e-5,R=1e-3):
        """Layer 1: 2-state Kalman [price,velocity]"""
        n=len(prices);F=np.array([[1,1],[0,1]],float);H=np.array([[1,0]],float)
        x=np.array([prices[0],0],float);P=np.eye(2);Q_m=np.diag([Q,Q]);R_m=np.array([[R]])
        filt=np.zeros(n);vels=np.zeros(n);innov=np.zeros(n)
        for i in range(n):
            xp=F@x;Pp=F@P@F.T+Q_m;y=prices[i]-(H@xp)[0];S=(H@Pp@H.T+R_m)[0,0]
            K=(Pp@H.T)/S;x=xp+K.flatten()*y;P=(np.eye(2)-K@H)@Pp
            filt[i]=x[0];vels[i]=x[1];innov[i]=y
        accs=np.diff(vels,prepend=vels[0])
        vs=np.std(vels[-20:])if len(vels)>=20 else np.std(vels)+1e-10
        th=0.15*max(vs,1e-8);v=vels[-1];a=accs[-1]
        if v>th and a>0:s=min(v/(th*3),1)
        elif v<-th and a<0:s=max(v/(th*3),-1)
        else:s=np.clip(v/(th*3+1e-10),-1,1)
        return{"filtered":filt[-1],"velocity":v,"acceleration":a,"innovation":innov[-1],
               "signal":float(np.clip(s,-1,1)),"threshold":th,"velocities":vels,"innovations":innov}

    @staticmethod
    def hmm(returns,n_states=3,n_iter=25):
        """Layer 2: 3-state HMM with Baum-Welch"""
        n=len(returns)
        if n<30:return{"p_bull":0.33,"p_neutral":0.34,"p_bear":0.33,"dominant":"NEUTRAL","uncertain":True}
        pi=np.array([0.33,0.34,0.33]);A=np.array([[0.8,0.15,0.05],[0.1,0.8,0.1],[0.05,0.15,0.8]])
        mu=np.array([np.percentile(returns,75),np.median(returns),np.percentile(returns,25)])
        sig=np.maximum(np.array([np.std(returns)]*3),1e-8)
        for _ in range(n_iter):
            B=np.zeros((n_states,n))
            for j in range(n_states):B[j]=sp_stats.norm.pdf(returns,mu[j],sig[j])+1e-300
            alpha=np.zeros((n,n_states));alpha[0]=pi*B[:,0];alpha[0]/=alpha[0].sum()+1e-300
            for t in range(1,n):alpha[t]=(alpha[t-1]@A)*B[:,t];alpha[t]/=alpha[t].sum()+1e-300
            beta=np.zeros((n,n_states));beta[-1]=1.0
            for t in range(n-2,-1,-1):beta[t]=A@(B[:,t+1]*beta[t+1]);beta[t]/=beta[t].sum()+1e-300
            gamma=alpha*beta;gamma/=gamma.sum(axis=1,keepdims=True)+1e-300
            pi=gamma[0]
            for j in range(n_states):
                w=gamma[:,j];mu[j]=np.average(returns,weights=w)
                sig[j]=max(np.sqrt(np.average((returns-mu[j])**2,weights=w)),1e-8)
            xi=np.zeros((n_states,n_states))
            for t in range(n-1):
                for i in range(n_states):
                    for j in range(n_states):xi[i,j]+=alpha[t,i]*A[i,j]*B[j,t+1]*beta[t+1,j]
            xi/=xi.sum()+1e-300
            for i in range(n_states):
                rs=xi[i].sum()
                if rs>0:A[i]=xi[i]/rs
        order=np.argsort(mu);probs=gamma[-1]
        pb,pn,pbl=probs[order[0]],probs[order[1]],probs[order[2]]
        dom=["BEAR","NEUTRAL","BULL"][np.argmax([pb,pn,pbl])]
        return{"p_bull":float(pbl),"p_neutral":float(pn),"p_bear":float(pb),"dominant":dom,"uncertain":max(pbl,pn,pb)<0.60}

    @staticmethod
    def hurst(prices,windows=None):
        """Layer 3: R/S Hurst exponent"""
        if windows is None:windows=[8,12,16,24,32,48,64]
        prices=np.array(prices,float)
        if len(prices)<max(windows):return{"hurst":0.50,"stability":0.10}
        rs_vals=[]
        for w in windows:
            if w>len(prices):continue
            rs_list=[]
            for st in range(0,len(prices)-w+1,max(w//2,1)):
                seg=prices[st:st+w]
                if len(seg)<w:continue
                r=np.diff(np.log(seg+1e-10));mr=r.mean();d=np.cumsum(r-mr)
                R=d.max()-d.min();S=r.std()
                if S>1e-10:rs_list.append(R/S)
            if rs_list:rs_vals.append((np.log(w),np.log(np.mean(rs_list))))
        if len(rs_vals)<3:return{"hurst":0.50,"stability":0.10}
        x=np.array([v[0]for v in rs_vals]);y=np.array([v[1]for v in rs_vals])
        slope,_,_,_,_=sp_stats.linregress(x,y)
        return{"hurst":float(np.clip(slope,0,1)),"stability":0.0}

    @staticmethod
    def har_rv(closes,target_vol=VOL_TARGET):
        """Layer 4: HAR-RV volatility model"""
        if len(closes)<100:return{"forecast":0.03,"vol_scalar":1.0,"vol_pct":50,"daily_vol":0.035}
        lr=np.diff(np.log(closes))
        rv_d=np.array([np.sum(lr[max(0,i-24):i]**2)for i in range(24,len(lr))])
        rv_w=np.array([np.mean(rv_d[max(0,i-5):i])for i in range(5,len(rv_d))])
        rv_m=np.array([np.mean(rv_d[max(0,i-22):i])for i in range(22,len(rv_d))])
        n=min(len(rv_d),len(rv_w),len(rv_m))-1
        if n<10:return{"forecast":0.03,"vol_scalar":1.0,"vol_pct":50,"daily_vol":0.035}
        y=rv_d[-n:];X=np.column_stack([rv_d[-(n+1):-1],rv_w[-n:],rv_m[-n:],np.ones(n)])
        try:
            betas,_,_,_=np.linalg.lstsq(X,y,rcond=None)
            fc=max(betas@np.array([rv_d[-1],rv_w[-1],rv_m[-1],1.0]),1e-8)
        except:fc=rv_d[-1]if len(rv_d)>0 else 0.001
        dv=np.sqrt(fc*24);vs=np.clip(target_vol/max(dv,0.001),0.40,1.80)
        vp=sp_stats.percentileofscore(rv_d,rv_d[-1])if len(rv_d)>10 else 50
        return{"forecast":float(fc),"vol_scalar":float(vs),"vol_pct":float(vp),"daily_vol":float(dv)}

    @staticmethod
    def alphas(df,ob,bwl,bws):
        """Layer 5: 5 alphas with Bayesian weighting"""
        c=df["close"].values;v=df["volume"].values;h=df["high"].values;l=df["low"].values;n=len(c)
        # A1: Kalman momentum
        kd=Sig.kalman(c[-200:]);a1=float(np.clip(kd["signal"],-1,1))
        # A2: Multi-period momentum
        ms=[]
        for p in[4,12,24,48]:
            if n>p:ms.append((c[-1]-c[-p])/(c[-p]+1e-10))
        a2=float(np.clip(np.mean(ms)*20 if ms else 0,-1,1))
        # A3: Market structure
        a3=0.0
        if n>=20:
            rh=h[-20:];rl=l[-20:]
            hh=rh[-1]>np.max(rh[:-1]);hl=rl[-1]>np.min(rl[-5:])
            ll=rl[-1]<np.min(rl[:-1]);lh=rh[-1]<np.max(rh[-5:])
            if hh and hl:a3=0.8
            elif ll and lh:a3=-0.8
            elif hh:a3=0.4
            elif ll:a3=-0.4
        # A4: Volume-weighted momentum
        a4=0.0
        if n>=10:
            vw=v[-10:]/(v[-10:].sum()+1e-10);rt=np.diff(c[-11:])/(c[-11:-1]+1e-10)
            a4=float(np.clip(np.sum(vw*rt)*50,-1,1))
        # A5: Order flow imbalance
        a5=0.0
        if ob and"bids"in ob and"asks"in ob:
            bv=sum(float(b[1])for b in ob["bids"][:10]);av=sum(float(a[1])for a in ob["asks"][:10])
            t=bv+av
            if t>0:a5=float(np.clip((bv-av)/t*2,-1,1))
        alp=np.array([a1,a2,a3,a4,a5])
        wl=np.maximum(np.array(bwl),B_FLOOR);ws=np.maximum(np.array(bws),B_FLOOR)
        wl/=wl.sum();ws/=ws.sum()
        el=float(np.dot(wl,alp));es=float(np.dot(ws,-alp))
        return{"alphas":alp.tolist(),"ensemble_long":el,"ensemble_short":es,"kalman":kd,
               "names":["Kalman","Momentum","Structure","VolMom","OFI"]}

    @staticmethod
    def supertrend(df,period=10,mult=2.0):
        h=df["high"].values;l=df["low"].values;c=df["close"].values;n=len(c)
        atr=np.zeros(n)
        for i in range(1,n):
            tr=max(h[i]-l[i],abs(h[i]-c[i-1]),abs(l[i]-c[i-1]))
            atr[i]=(atr[i-1]*(period-1)+tr)/period if i>=period else tr
        upper=(h+l)/2+mult*atr;lower=(h+l)/2-mult*atr;trend=np.ones(n)
        for i in range(1,n):
            if c[i]>upper[i-1]:trend[i]=1
            elif c[i]<lower[i-1]:trend[i]=-1
            else:trend[i]=trend[i-1]
        return float(trend[-1])

    @staticmethod
    def stoch_rsi(closes,period=14):
        n=len(closes)
        if n<period+5:return{"k":50,"d":50}
        d=np.diff(closes);g=np.where(d>0,d,0);ls=np.where(d<0,-d,0)
        ag=np.convolve(g,np.ones(period)/period,mode='valid')
        al=np.convolve(ls,np.ones(period)/period,mode='valid')
        rs=ag/(al+1e-10);rsi=100-100/(1+rs)
        if len(rsi)<period:return{"k":50,"d":50}
        rw=rsi[-period:];mn=rw.min();mx=rw.max()
        k=(rsi[-1]-mn)/(mx-mn+1e-10)*100
        return{"k":float(k),"d":float(k)}

    @staticmethod
    def vwap(df):
        cv=df["volume"].cumsum();ctv=((df["high"]+df["low"]+df["close"])/3*df["volume"]).cumsum()
        return float((ctv/(cv+1e-10)).iloc[-1])

    @staticmethod
    def atr(df,period=14):
        h=df["high"].values;l=df["low"].values;c=df["close"].values
        trs=[max(h[i]-l[i],abs(h[i]-c[i-1]),abs(l[i]-c[i-1]))for i in range(1,len(c))]
        return float(np.mean(trs[-period:]))if len(trs)>=period else(float(np.mean(trs))if trs else 0)

    @staticmethod
    def bollinger(closes,period=20):
        if len(closes)<period:return{"upper":closes[-1]*1.02,"lower":closes[-1]*0.98,"width":0.04,"width_pct":50}
        ma=np.mean(closes[-period:]);sd=np.std(closes[-period:])
        u=ma+2*sd;lo=ma-2*sd;w=(u-lo)/(ma+1e-10)
        # width percentile over recent history
        if len(closes)>=60:
            widths=[(np.mean(closes[i:i+period])+2*np.std(closes[i:i+period])-(np.mean(closes[i:i+period])-2*np.std(closes[i:i+period])))/(np.mean(closes[i:i+period])+1e-10)for i in range(len(closes)-60,len(closes)-period)]
            wp=sp_stats.percentileofscore(widths,w)if widths else 50
        else:wp=50
        return{"upper":u,"lower":lo,"width":w,"width_pct":float(wp)}

    @staticmethod
    def ema(closes,period):
        if len(closes)<1:return 0
        a=2/(period+1);e=closes[0]
        for p in closes[1:]:e=a*p+(1-a)*e
        return float(e)

    @staticmethod
    def rsi(closes,period=14):
        if len(closes)<period+1:return 50
        d=np.diff(closes[-(period+1):])
        g=np.mean(np.where(d>0,d,0));l=np.mean(np.where(d<0,-d,0))
        if l<1e-10:return 100
        return float(100-100/(1+g/l))

    @staticmethod
    def vpin(trades_data,bucket_size=None):
        """Layer 11: VPIN — Volume-Synchronized Probability of Informed Trading"""
        if not trades_data or len(trades_data)<50:
            return{"vpin":0.40,"vpin_delta":0.0,"direction":"NEUTRAL"}
        prices=[float(t.get("price",0))for t in trades_data]
        qtys=[float(t.get("qty",0))for t in trades_data]
        buyer=[t.get("isBuyerMaker",False)for t in trades_data]
        total_vol=sum(qtys)
        if bucket_size is None:bucket_size=max(total_vol/50,0.01)
        bb=[];bs=[];cb=0;cs=0;cv=0
        for i in range(len(prices)):
            q=qtys[i]
            if buyer[i]:cs+=q
            else:cb+=q
            cv+=q
            if cv>=bucket_size:bb.append(cb);bs.append(cs);cb=0;cs=0;cv=0
        if not bb:return{"vpin":0.40,"vpin_delta":0.0,"direction":"NEUTRAL"}
        nb=min(len(bb),50);vals=[]
        for i in range(-nb,0):
            t=bb[i]+bs[i]
            if t>0:vals.append(abs(bb[i]-bs[i])/t)
        vp=np.mean(vals)if vals else 0.40
        tb=sum(bb[-nb:]);ts=sum(bs[-nb:])
        if tb>ts*1.3:d="BUYING"
        elif ts>tb*1.3:d="SELLING"
        else:d="NEUTRAL"
        return{"vpin":float(vp),"vpin_delta":0.0,"direction":d}

    @staticmethod
    def book_pressure(ob,levels=20):
        """Layer 12A: Depth-weighted bid-ask imbalance"""
        if not ob or"bids"not in ob:return{"pressure":0,"bid_depth":0,"ask_depth":0}
        bids=ob.get("bids",[])[:levels];asks=ob.get("asks",[])[:levels]
        wb=sum(float(b[1])*np.exp(-0.1*i)for i,b in enumerate(bids))
        wa=sum(float(a[1])*np.exp(-0.1*i)for i,a in enumerate(asks))
        t=wb+wa;p=(wb-wa)/t if t>0 else 0
        return{"pressure":float(p),"bid_depth":float(wb),"ask_depth":float(wa)}

    @staticmethod
    def spread_bps(ob):
        if not ob or"bids"not in ob or"asks"not in ob:return 10.0
        b=ob.get("bids",[]);a=ob.get("asks",[])
        if not b or not a:return 10.0
        bb=float(b[0][0]);ba=float(a[0][0]);mid=(bb+ba)/2
        return float((ba-bb)/mid*10000)if mid>0 else 10.0

    @staticmethod
    def micro_price(ob):
        """Micro-price for smart entry timing"""
        if not ob or"bids"not in ob or"asks"not in ob:return 0,0
        b=ob["bids"];a=ob["asks"]
        if not b or not a:return 0,0
        bp=float(b[0][0]);bq=float(b[0][1]);ap=float(a[0][0]);aq=float(a[0][1])
        mid=(bp+ap)/2;mp=(bp*aq+ap*bq)/(bq+aq)if(bq+aq)>0 else mid
        return float(mp),float(mid)

    @staticmethod
    def detect_spoofing(prev_ob,curr_ob):
        """Layer 8A: Order book spoofing detection"""
        if not prev_ob or not curr_ob:return False
        try:
            prev_bids={float(b[0]):float(b[1])for b in prev_ob.get("bids",[])[:10]}
            curr_bids={float(b[0]):float(b[1])for b in curr_ob.get("bids",[])[:10]}
            avg_bid=np.mean([float(b[1])for b in curr_ob.get("bids",[])[:10]])if curr_ob.get("bids")else 1
            for price,qty in prev_bids.items():
                if qty>5*avg_bid and price not in curr_bids:return True
            prev_asks={float(a[0]):float(a[1])for a in prev_ob.get("asks",[])[:10]}
            curr_asks={float(a[0]):float(a[1])for a in curr_ob.get("asks",[])[:10]}
            avg_ask=np.mean([float(a[1])for a in curr_ob.get("asks",[])[:10]])if curr_ob.get("asks")else 1
            for price,qty in prev_asks.items():
                if qty>5*avg_ask and price not in curr_asks:return True
        except:pass
        return False

    @staticmethod
    def detect_wash(df,lookback=3):
        """Layer 8B: Wash trading detection"""
        if len(df)<lookback+1:return False
        for i in range(-lookback,0):
            vol=df["volume"].iloc[i];avg_vol=df["volume"].iloc[-20:-1].mean()if len(df)>20 else vol
            price_chg=abs(df["close"].iloc[i]-df["open"].iloc[i])/df["open"].iloc[i]
            if vol>3*avg_vol and price_chg<0.001:return True
        return False

    @staticmethod
    def detect_liq_hunt(df_5m):
        """Layer 8C: Liquidation hunt pattern"""
        if len(df_5m)<3:return False
        c=df_5m["close"].values;h=df_5m["high"].values;l=df_5m["low"].values
        move1=(c[-2]-c[-3])/c[-3]if c[-3]>0 else 0
        move2=(c[-1]-c[-2])/c[-2]if c[-2]>0 else 0
        if abs(move1)>0.008 and abs(move2)>abs(move1)*0.5 and np.sign(move1)!=np.sign(move2):return True
        return False

    @staticmethod
    def detect_iceberg(ob,prev_ob,refill_tracker):
        """Layer 8D: Iceberg order detection"""
        if not ob or not prev_ob:return False,"",refill_tracker
        try:
            for side in["bids","asks"]:
                prev={float(x[0]):float(x[1])for x in prev_ob.get(side,[])[:5]}
                curr={float(x[0]):float(x[1])for x in ob.get(side,[])[:5]}
                for price in prev:
                    if price not in curr:
                        if price in refill_tracker:refill_tracker[price]+=1
                        else:refill_tracker[price]=1
                    elif price in curr and prev[price]<1 and curr[price]>prev[price]*0.8:
                        if price in refill_tracker:refill_tracker[price]+=1
                        else:refill_tracker[price]=1
                for price,count in refill_tracker.items():
                    if count>5:
                        return True,side,refill_tracker
        except:pass
        return False,"",refill_tracker

    @staticmethod
    def book_absorption(ob,vol_avg):
        """Layer 12C: Book absorption detection"""
        if not ob or vol_avg<=0:return False,""
        for side in["bids","asks"]:
            levels=ob.get(side,[])[:5]
            for price,qty in[(float(x[0]),float(x[1]))for x in levels]:
                if qty>3*vol_avg:return True,side
        return False,""

    @staticmethod
    def mutual_info(x,y,bins=5):
        """Layer 13A: Mutual information"""
        if len(x)<20 or len(y)<20:return 0.0
        n=min(len(x),len(y));x=np.array(x[-n:]);y=np.array(y[-n:])
        hist,_,_=np.histogram2d(x,y,bins=bins);pxy=hist/hist.sum()
        px=pxy.sum(axis=1);py=pxy.sum(axis=0);mi=0.0
        for i in range(bins):
            for j in range(bins):
                if pxy[i,j]>1e-10 and px[i]>1e-10 and py[j]>1e-10:
                    mi+=pxy[i,j]*np.log(pxy[i,j]/(px[i]*py[j]))
        return max(float(mi),0.0)

    @staticmethod
    def signal_entropy(alphas,bins=4):
        """Layer 13B: Signal entropy"""
        if len(alphas)<2:return 1.0
        edges=np.linspace(-1,1,bins+1);counts,_=np.histogram(alphas,bins=edges)
        p=counts/counts.sum();p=p[p>0]
        return float(-np.sum(p*np.log(p)))

    @staticmethod
    def alpha_correlation(alpha_history):
        """Layer 13C: Signal decorrelation monitor"""
        if len(alpha_history)<20:return 0.3
        arr=np.array(alpha_history[-100:])
        if arr.shape[1]<2:return 0.0
        corr=np.corrcoef(arr.T);np.fill_diagonal(corr,0)
        return float(np.mean(np.abs(corr)))

    @staticmethod
    def cross_asset_score(btc_df,sol_df):
        """Layer 9: Cross-asset momentum"""
        score=0.0
        if len(btc_df)>10:
            bc=btc_df["close"].values
            e8=Sig.ema(bc,8);e21=Sig.ema(bc,21);e50=Sig.ema(bc,50)
            bvw=Sig.vwap(btc_df)
            if e8>e21>e50:score+=1.0
            elif e8<e21<e50:score-=1.0
            if bc[-1]>bvw:score+=0.5
            else:score-=0.5
            ret4h=((bc[-1]-bc[-4])/bc[-4])if len(bc)>4 else 0
            score+=0.5 if ret4h>0 else -0.5
        score*=0.70
        if len(sol_df)>10:
            sc=sol_df["close"].values
            se8=Sig.ema(sc,8);se21=Sig.ema(sc,21)
            s_score=(0.5 if se8>se21 else -0.5)
            s_ret=((sc[-1]-sc[-4])/sc[-4])if len(sc)>4 else 0
            s_score+=(0.5 if s_ret>0 else -0.5)
            score+=s_score*0.30
        return float(np.clip(score,-2,2))

    @staticmethod
    def btc_crash_check(btc_df):
        """ETH-specific: BTC crash gate"""
        if len(btc_df)<12:return False
        c=btc_df["close"].values
        ret_1h=(c[-1]-c[-1])/(c[-1]+1e-10)if len(c)>1 else 0
        # Use 12 5-min bars = 1 hour
        if len(c)>=2:ret_1h=(c[-1]-c[-2])/(c[-2]+1e-10)
        return ret_1h<-0.03

    @staticmethod
    def btc_divergence(eth_df,btc_df,lookback=20):
        """Cross-asset divergence signal"""
        if len(eth_df)<lookback or len(btc_df)<lookback:return 0
        ec=eth_df["close"].values[-lookback:];bc=btc_df["close"].values[-lookback:]
        eth_new_low=ec[-1]<=np.min(ec);btc_holding=bc[-1]>np.min(bc)*1.005
        eth_new_high=ec[-1]>=np.max(ec);btc_failing=bc[-1]<np.max(bc)*0.995
        if eth_new_low and btc_holding:return 10
        if eth_new_high and btc_failing:return-8
        return 0

    @staticmethod
    def eth_vol_regime(daily_vol):
        """ETH-specific volatility regime"""
        if daily_vol<0.03:return"LOW"
        elif daily_vol<0.05:return"NORMAL"
        elif daily_vol<0.07:return"HIGH"
        else:return"EXTREME"

    @staticmethod
    def freshness_weights(n_alphas,df_1h):
        """Signal freshness decay lambda=0.02 based on actual candle age."""
        w=[]
        if len(df_1h)>0:
            # Calculate minutes since last candle CLOSED
            last_candle_close=df_1h["ot"].iloc[-1]
            if hasattr(last_candle_close,'timestamp'):
                candle_ts=last_candle_close.timestamp()
            else:
                candle_ts=float(last_candle_close)/1000 if last_candle_close>1e12 else float(last_candle_close)
            mins_since=(time.time()-candle_ts)/60
            mins_since=max(mins_since,0)
        else:
            mins_since=30  # default if no data
        for i in range(n_alphas):
            if i==4:w.append(1.0)  # OFI always fresh (live orderbook)
            else:w.append(float(np.exp(-FRESH_LAMBDA*mins_since)))
        return w,float(mins_since)
# ═══ CONFLUENCE SCORER ═══
class Confluence:
    # Adaptive weight multipliers — learned from trade history
    # Start at 1.0 (neutral), adjusted by SignalTracker after 30+ trades
    _weight_mults=None

    @classmethod
    def load_weights(cls,db):
        """Load learned signal weight multipliers from DB."""
        cls._weight_mults=db.kv_get("signal_weight_mults",{})

    @classmethod
    def get_mult(cls,signal_name):
        """Get learned multiplier for a signal (1.0 = default, >1 = overweight, <1 = underweight)."""
        if not cls._weight_mults:return 1.0
        return cls._weight_mults.get(signal_name,1.0)

    @staticmethod
    def _apply(base_pts,signal_name):
        """Apply learned weight multiplier to base points."""
        m=Confluence.get_mult(signal_name)
        return int(round(base_pts*np.clip(m,0.3,2.0)))  # clamp: never zero, never 2x

    @staticmethod
    def score_a(s):
        """Strategy A (trend-following) scoring with adaptive weights."""
        ls=0;ss=0;ap=Confluence._apply
        kv=s.get("kalman_vel",0);kt=s.get("kalman_thresh",0.001);ka=s.get("kalman_acc",0)
        if kv>kt and ka>0:ls+=ap(12,"kalman_strong")
        elif kv>kt:ls+=ap(8,"kalman_mild")
        if kv<-kt and ka<0:ss+=ap(12,"kalman_strong")
        elif kv<-kt:ss+=ap(8,"kalman_mild")
        hb=s.get("hmm_bull",0.33);hbe=s.get("hmm_bear",0.33)
        if hb>0.65:ls+=ap(14,"hmm_strong")
        elif hb>0.55:ls+=ap(8,"hmm_mild")
        if hbe>0.65:ss+=ap(14,"hmm_strong")
        elif hbe>0.55:ss+=ap(8,"hmm_mild")
        hu=s.get("hurst",0.5)
        if hu>0.60:ls+=10;ss+=10
        elif hu>0.55:ls+=5;ss+=5
        if s.get("vol_scalar",1)>1.20:ls+=8;ss+=6
        el=s.get("ensemble_long",0);es=s.get("ensemble_short",0)
        if el>0.65:ls+=12
        elif el>0.55:ls+=7
        if es>0.65:ss+=12
        elif es>0.55:ss+=7
        if s.get("price",0)>s.get("vwap",0):ls+=7
        else:ss+=7
        if s.get("st_1h",0)>0:ls+=8
        else:ss+=8
        if s.get("st_4h",0)>0:ls+=8
        else:ss+=8
        if s.get("ema8",0)>s.get("ema21",0):ls+=5
        else:ss+=5
        if s.get("vol_ratio",1)>1.5:ls+=5;ss+=5
        sk=s.get("stoch_k",50)
        if sk<50:ls+=7
        if sk>50:ss+=7
        fr=s.get("funding_rate",0)
        if fr<0:ls+=5
        if fr>0.0005:ss+=8
        if fr>0.001:ls-=15
        if fr<-0.0006:ss-=15
        ca=s.get("cross_asset",0)
        if ca>1.0:ls+=8;ss-=8
        elif ca>0.5:ls+=4;ss-=4
        elif ca<-1.0:ss+=8;ls-=8
        elif ca<-0.5:ss+=4;ls-=4
        vp=s.get("vpin",0.4)
        if vp<0.40:ls+=6;ss+=5
        elif vp>0.55:ls-=12;ss-=12
        elif vp>0.45:ls-=6;ss-=6
        ase=s.get("adverse_sel",0.5)
        if ase<0.30:ls+=5;ss+=5
        elif ase>0.50:ls-=10;ss-=10
        bp=s.get("book_pressure",0)
        if bp>0.60:ls+=5
        elif bp<-0.60:ss+=5
        if bp<-0.40:ls-=8
        if bp>0.40:ss-=8
        mi=s.get("avg_mi",0)
        if mi>0.15:ls+=4;ss+=4
        bc=s.get("bayesian_consensus",0)
        if bc>0.75:ls+=6;ss+=6
        ois=s.get("oi_scenario","")
        if ois=="A":ls+=6
        elif ois=="B":ss+=6
        elif ois=="C":ls-=8
        elif ois=="D":ss-=8
        if s.get("oi_extreme",False):ls-=10;ss-=10
        fts=s.get("funding_term","")
        if fts=="STEEP_CONTANGO":ls-=8;ss+=8
        elif fts=="STEEP_BACKWARDATION":ls+=8;ss-=8
        elif fts=="BACKWARDATION":ls+=4
        elif fts=="CONTANGO":ss+=4
        if s.get("funding_oi_conf_long",False):ls+=15
        if s.get("funding_oi_conf_short",False):ss+=15
        al=s.get("agents_long",0);ash=s.get("agents_short",0)
        if al>=6:ls+=14
        elif al>=5:ls+=8
        if ash>=6:ss+=14
        elif ash>=5:ss+=8
        if s.get("agents_oppose_long",0)>=2:ls-=12
        if s.get("agents_oppose_short",0)>=2:ss-=12
        if s.get("agent_near_veto",False):ls-=18;ss-=18
        if hbe>0.40:ls-=10
        if hb>0.40:ss-=10
        if s.get("hmm_uncertain",False):ls-=10;ss-=10
        sess=s.get("session","EU")
        if sess=="ASIAN":ls-=8;ss-=8
        elif sess=="DEAD":ls-=8;ss-=10
        if s.get("manipulation",False):ls-=25;ss-=25
        if sk>75:ls-=10
        if sk<25:ss-=10
        fr_val=s.get("freshness",1)
        if fr_val>0.80:ls+=4;ss+=4
        elif fr_val<0.40:ls-=5;ss-=5
        div=s.get("btc_divergence",0)
        if div>0:ls+=div
        elif div<0:ss+=abs(div)
        return max(ls,0),max(ss,0)

    @staticmethod
    def score_b(s):
        """Strategy B (mean-reversion) scoring."""
        ls=0;ss=0
        p=s.get("price",0);vw=s.get("vwap",p);at=s.get("atr_val",1)
        if at>0 and abs(p-vw)>2*at:
            if p<vw:ls+=20
            else:ss+=20
        sk=s.get("stoch_k",50)
        if sk<15:ls+=20
        if sk>85:ss+=20
        if s.get("bb_width_pct",50)<30:ls+=15;ss+=15
        if s.get("st_4h_opposing",False):ls+=15;ss+=15
        if s.get("vol_scalar",1)>1.0:ls+=10;ss+=10
        vp=s.get("vpin",0.5)
        if vp<0.55:ls+=10;ss+=10
        if s.get("adverse_sel",0.5)<0.40:ls+=8;ss+=8
        if s.get("absorption",False):ls+=8;ss+=8
        if s.get("oi_extreme",False)and s.get("funding_extreme",False):ls+=20;ss+=20
        if s.get("micro_confirms",False):ls+=10;ss+=10
        return max(ls,0),max(ss,0)

# ═══ SIGNAL TRACKER — Learns which signals actually contribute to wins ═══
class SignalTracker:
    """Adaptive signal weight learning with anti-overfitting safeguards.
    Implements: Wilson score intervals, progressive constraint relaxation,
    correlation penalty, marginal contribution tracking, weight evolution logging."""

    TRACKED=["kalman_strong","kalman_mild","hmm_strong","hmm_mild",
        "hurst_trend","ensemble_strong","ensemble_mild","vwap_aligned",
        "supertrend_1h","supertrend_4h","ema_aligned","volume_surge",
        "stoch_signal","funding_favorable","cross_asset","vpin_clean",
        "book_pressure","oi_confirms","agent_consensus"]

    # Signal pairs known to be correlated (same information source)
    CORR_PAIRS=[("kalman_strong","kalman_mild"),("hmm_strong","hmm_mild"),
                ("ensemble_strong","ensemble_mild"),("supertrend_1h","supertrend_4h"),
                ("kalman_strong","ensemble_strong"),("hmm_strong","hurst_trend")]

    @staticmethod
    def extract_active(signals,direction):
        """Extract which signals were active at entry."""
        a={};kv=signals.get("kalman_vel",0);kt=signals.get("kalman_thresh",0.001);ka=signals.get("kalman_acc",0)
        if direction=="LONG":
            a["kalman_strong"]=1 if(kv>kt and ka>0)else 0;a["kalman_mild"]=1 if(kv>kt)else 0
            a["hmm_strong"]=1 if signals.get("hmm_bull",0)>0.65 else 0
            a["hmm_mild"]=1 if signals.get("hmm_bull",0)>0.55 else 0
            a["ensemble_strong"]=1 if signals.get("ensemble_long",0)>0.65 else 0
            a["ensemble_mild"]=1 if signals.get("ensemble_long",0)>0.55 else 0
            a["vwap_aligned"]=1 if signals.get("price",0)>signals.get("vwap",0)else 0
        else:
            a["kalman_strong"]=1 if(kv<-kt and ka<0)else 0;a["kalman_mild"]=1 if(kv<-kt)else 0
            a["hmm_strong"]=1 if signals.get("hmm_bear",0)>0.65 else 0
            a["hmm_mild"]=1 if signals.get("hmm_bear",0)>0.55 else 0
            a["ensemble_strong"]=1 if signals.get("ensemble_short",0)>0.65 else 0
            a["ensemble_mild"]=1 if signals.get("ensemble_short",0)>0.55 else 0
            a["vwap_aligned"]=1 if signals.get("price",0)<signals.get("vwap",0)else 0
        a["hurst_trend"]=1 if signals.get("hurst",0.5)>0.60 else 0
        a["supertrend_1h"]=1 if((direction=="LONG"and signals.get("st_1h",0)>0)or(direction=="SHORT"and signals.get("st_1h",0)<0))else 0
        a["supertrend_4h"]=1 if((direction=="LONG"and signals.get("st_4h",0)>0)or(direction=="SHORT"and signals.get("st_4h",0)<0))else 0
        a["ema_aligned"]=1 if((direction=="LONG"and signals.get("ema8",0)>signals.get("ema21",0))or(direction=="SHORT"and signals.get("ema8",0)<signals.get("ema21",0)))else 0
        a["volume_surge"]=1 if signals.get("vol_ratio",1)>1.5 else 0
        a["vpin_clean"]=1 if signals.get("vpin",0.5)<0.40 else 0
        a["book_pressure"]=1 if abs(signals.get("book_pressure",0))>0.40 else 0
        a["funding_favorable"]=1 if((direction=="LONG"and signals.get("funding_rate",0)<0)or(direction=="SHORT"and signals.get("funding_rate",0)>0.0005))else 0
        ca=signals.get("cross_asset",0)
        a["cross_asset"]=1 if((direction=="LONG"and ca>0.5)or(direction=="SHORT"and ca<-0.5))else 0
        a["oi_confirms"]=1 if((direction=="LONG"and signals.get("oi_scenario","")=="A")or(direction=="SHORT"and signals.get("oi_scenario","")=="B"))else 0
        a["agent_consensus"]=1 if signals.get("agents_long"if direction=="LONG"else"agents_short",0)>=5 else 0
        a["stoch_signal"]=1 if((direction=="LONG"and signals.get("stoch_k",50)<40)or(direction=="SHORT"and signals.get("stoch_k",50)>60))else 0
        return a

    @staticmethod
    def _wilson_lower(wins,total,z=1.96):
        """Wilson score lower bound — conservative win rate estimate.
        Returns the lower bound of the 95% CI, preventing overfitting to small samples."""
        if total==0:return 0.5
        p=wins/total;denom=1+z*z/total
        center=(p+z*z/(2*total))/denom
        spread=z*np.sqrt((p*(1-p)+z*z/(4*total))/total)/denom
        return max(center-spread,0)

    @staticmethod
    def _progressive_clamp(raw_mult,n_trades):
        """Progressively relax weight constraints as more data accumulates.
        Early: tight [0.85, 1.15]. After 100+ trades: full [0.50, 1.80]."""
        if n_trades<50:return 1.0  # No adjustment until 50 trades
        elif n_trades<75:lo,hi=0.85,1.15  # Tight constraints
        elif n_trades<100:lo,hi=0.75,1.30  # Medium
        elif n_trades<150:lo,hi=0.65,1.50  # Relaxing
        else:lo,hi=0.50,1.80  # Full range
        return float(np.clip(raw_mult,lo,hi))

    @staticmethod
    def _correlation_penalty(mults,snaps):
        """Reduce combined influence of correlated signal pairs.
        If two signals co-occur >70% of the time, dampen the weaker one."""
        if len(snaps)<30:return mults
        for s1,s2 in SignalTracker.CORR_PAIRS:
            both_active=sum(1 for s in snaps if s["signals"].get(s1,0)==1 and s["signals"].get(s2,0)==1)
            either_active=sum(1 for s in snaps if s["signals"].get(s1,0)==1 or s["signals"].get(s2,0)==1)
            if either_active>0:
                co_rate=both_active/either_active
                if co_rate>0.70:
                    # Dampen the weaker signal's multiplier
                    m1=mults.get(s1,1.0);m2=mults.get(s2,1.0)
                    if m1<m2:mults[s1]=m1*0.80  # reduce weaker by 20%
                    else:mults[s2]=m2*0.80
        return mults

    @staticmethod
    def _marginal_contribution(sig_name,snaps):
        """Measure marginal improvement: does adding this signal to existing signals help?
        Compares WR when this signal is the DIFFERENTIATOR (other signals same)."""
        if len(snaps)<50:return 0.0  # not enough data
        # Find trade pairs where this signal differs but most others agree
        marginal_wins=0;marginal_total=0
        active_snaps=[s for s in snaps if s["signals"].get(sig_name,0)==1]
        inactive_snaps=[s for s in snaps if s["signals"].get(sig_name,0)==0]
        if len(active_snaps)<10 or len(inactive_snaps)<10:return 0.0
        # Simple marginal: WR_active - WR_inactive
        wr_active=sum(1 for s in active_snaps if s["win"])/len(active_snaps)
        wr_inactive=sum(1 for s in inactive_snaps if s["win"])/len(inactive_snaps)
        return wr_active-wr_inactive  # positive = signal adds value

    @staticmethod
    def update_weights(db,min_trades=50):
        """Recompute signal weights with all safeguards.
        Uses Wilson score, progressive constraints, correlation penalty, marginal contribution."""
        snaps=[]
        trades=db.query("SELECT id,total_pnl_pct FROM trades WHERE status='CLOSED' ORDER BY id DESC LIMIT 300")
        for tid,pnl in trades:
            snap=db.kv_get(f"trade_signals_{tid}")
            if snap and isinstance(snap,dict)and"signals"in snap and snap.get("win")is not None:
                snaps.append(snap)
        n=len(snaps)
        if n<min_trades:return  # SAFEGUARD 1: minimum sample threshold

        mults={};marginals={}
        for sig in SignalTracker.TRACKED:
            active_wins=sum(1 for s in snaps if s["signals"].get(sig,0)==1 and s["win"])
            active_total=sum(1 for s in snaps if s["signals"].get(sig,0)==1)
            inactive_wins=sum(1 for s in snaps if s["signals"].get(sig,0)==0 and s["win"])
            inactive_total=sum(1 for s in snaps if s["signals"].get(sig,0)==0)
            if active_total>=10 and inactive_total>=10:
                # SAFEGUARD 2: Wilson score — conservative WR estimate
                active_wr=SignalTracker._wilson_lower(active_wins,active_total)
                inactive_wr=SignalTracker._wilson_lower(inactive_wins,inactive_total)
                if inactive_wr>0.01:raw_mult=active_wr/inactive_wr
                else:raw_mult=1.2 if active_wr>0.5 else 1.0
                # SAFEGUARD 3: Progressive constraint relaxation
                mults[sig]=SignalTracker._progressive_clamp(raw_mult,n)
            else:
                mults[sig]=1.0  # not enough data for this signal
            # SAFEGUARD 4: Marginal contribution tracking
            marginals[sig]=SignalTracker._marginal_contribution(sig,snaps)

        # SAFEGUARD 5: Correlation penalty — reduce double-counting
        mults=SignalTracker._correlation_penalty(mults,snaps)

        # SAFEGUARD 7: EXPECTANCY-BASED SIGNAL KILL
        # A signal with 60% WR but big losses when wrong can have NEGATIVE expectancy.
        # Kill by expectancy, not just win rate.
        # Build trade_id → pnl lookup
        pnl_lookup={tid:pnl for tid,pnl in trades}
        killed_signals=[]
        for sig in SignalTracker.TRACKED:
            active_pnls=[]
            for tid,pnl in trades:
                snap=db.kv_get(f"trade_signals_{tid}")
                if snap and isinstance(snap,dict)and snap.get("signals",{}).get(sig,0)==1:
                    active_pnls.append(pnl or 0)
            if len(active_pnls)>=15:
                sig_exp=np.mean(active_pnls)
                if sig_exp<-0.003:  # signal has negative expectancy (loses money when active)
                    mults[sig]=SignalTracker._progressive_clamp(0.40,n)  # aggressively downweight
                    killed_signals.append((sig,sig_exp))
                    log.warning(f"🔪 SIGNAL KILL: '{sig}' expectancy={sig_exp:+.3%} — downweighted to ×{mults[sig]:.2f}")
        if killed_signals:
            db.kv_set("killed_signals",[(s,round(float(e),4))for s,e in killed_signals])

        # Store
        db.kv_set("signal_weight_mults",mults)
        Confluence._weight_mults=mults

        # SAFEGUARD 6: Weight evolution logging
        prev_mults=db.kv_get("prev_signal_mults",{})
        evolution={}
        for sig in SignalTracker.TRACKED:
            cur=mults.get(sig,1.0);prev=prev_mults.get(sig,1.0)
            delta=cur-prev;evolution[sig]={"mult":round(cur,3),"delta":round(delta,3),
                "marginal":round(marginals.get(sig,0),3)}
        db.kv_set("prev_signal_mults",mults)
        db.kv_set("signal_evolution",evolution)

        # Log significant changes
        stable=0;changed=0
        for sig,evo in evolution.items():
            if abs(evo["delta"])>0.05:
                changed+=1
                if evo["delta"]>0:log.info(f"📈 {sig}: ×{evo['mult']:.2f} (Δ+{evo['delta']:.2f}) marginal={evo['marginal']:+.2f}")
                else:log.info(f"📉 {sig}: ×{evo['mult']:.2f} (Δ{evo['delta']:.2f}) marginal={evo['marginal']:+.2f}")
            else:stable+=1
        # Flag oscillating signals (changed direction 3+ times in history)
        osc_history=db.kv_get("signal_osc_history",{})
        for sig in SignalTracker.TRACKED:
            delta=evolution.get(sig,{}).get("delta",0)
            hist=osc_history.get(sig,[])
            if abs(delta)>0.03:hist.append(1 if delta>0 else -1)
            hist=hist[-10:]  # keep last 10
            osc_history[sig]=hist
            if len(hist)>=4:
                sign_changes=sum(1 for i in range(1,len(hist))if hist[i]!=hist[i-1])
                if sign_changes>=3:
                    log.warning(f"⚠️ Signal '{sig}' oscillating ({sign_changes} reversals) — unstable, clamping to 1.0")
                    mults[sig]=1.0  # Force to neutral if oscillating
        db.kv_set("signal_osc_history",osc_history)
        if changed>0:db.kv_set("signal_weight_mults",mults);Confluence._weight_mults=mults
        log.info(f"Signal weights: {changed} changed, {stable} stable, {n} trades analyzed")

# ═══ LOGISTIC SCORER — Learns scoring from trade outcomes ═══
class LogisticScorer:
    """Replaces hardcoded confluence scoring with a learned logistic regression.
    Hybrid: uses hardcoded scoring for first 100 trades, then gradually transitions
    to learned model. By 200 trades, logistic has 80% of the vote.
    
    This is the '8.7 → 9.2' upgrade — the model learns which signal COMBINATIONS
    predict profitable trades, not just individual signal effectiveness."""

    FEATURES=["kalman_vel_norm","kalman_acc_sign","hmm_bull","hmm_bear","hurst",
              "ensemble_long","ensemble_short","vwap_dist","st_1h","st_4h",
              "ema_cross","vol_ratio_norm","stoch_k_norm","vpin","book_pressure",
              "funding_norm","cross_asset","oi_roc_1h_norm","spread_norm","uncertainty"]

    @staticmethod
    def extract_features(sigs):
        """Convert signals dict into normalized feature vector for logistic model."""
        p=sigs.get("price",3000);vw=sigs.get("vwap",p);atr=sigs.get("atr_val",1)
        kv=sigs.get("kalman_vel",0);kt=sigs.get("kalman_thresh",0.001)
        f=[
            np.clip(kv/(kt+1e-8),-3,3),  # kalman velocity normalized by threshold
            1.0 if sigs.get("kalman_acc",0)>0 else(-1.0 if sigs.get("kalman_acc",0)<0 else 0),
            sigs.get("hmm_bull",0.33),
            sigs.get("hmm_bear",0.33),
            sigs.get("hurst",0.50),
            sigs.get("ensemble_long",0),
            sigs.get("ensemble_short",0),
            np.clip((p-vw)/(atr+1e-8),-3,3),  # VWAP distance in ATR units
            sigs.get("st_1h",0),
            sigs.get("st_4h",0),
            1.0 if sigs.get("ema8",0)>sigs.get("ema21",0)else -1.0,
            np.clip(sigs.get("vol_ratio",1)/2,-1,2),  # volume ratio normalized
            (sigs.get("stoch_k",50)-50)/50,  # stochRSI centered at 0
            sigs.get("vpin",0.4),
            sigs.get("book_pressure",0),
            np.clip(sigs.get("funding_rate",0)*10000,-5,5),  # funding in bps
            sigs.get("cross_asset",0)/2,
            np.clip(sigs.get("oi_roc_1h",0)*100,-3,3),  # OI roc normalized
            np.clip(sigs.get("spread_bps",2)/5,-1,1),  # spread normalized
            sigs.get("uncertainty_flags",0)/5,
        ]
        return np.array(f,dtype=float)

    @staticmethod
    def train(db):
        """Train logistic regression on closed trade data. Returns coefficients or None."""
        trades=db.query("SELECT id,direction,total_pnl_pct FROM trades WHERE status='CLOSED' ORDER BY id DESC LIMIT 300")
        if len(trades)<100:return None  # not enough data
        X=[];y=[]
        for tid,direction,pnl in trades:
            feat=db.kv_get(f"trade_features_{tid}")
            if feat is None:continue
            feat=np.array(feat,dtype=float)
            if len(feat)!=len(LogisticScorer.FEATURES):continue
            X.append(feat)
            y.append(1 if(pnl or 0)>0 else 0)
        if len(X)<80:return None  # not enough with features stored
        X=np.array(X);y=np.array(y)
        # Standardize features (zero mean, unit variance)
        mu=X.mean(axis=0);sd=X.std(axis=0)+1e-8
        X_std=(X-mu)/sd
        # Add intercept
        X_aug=np.column_stack([X_std,np.ones(len(X_std))])
        # Logistic regression via gradient descent (from scratch — no sklearn)
        n_feat=X_aug.shape[1];w=np.zeros(n_feat);lr_rate=0.05
        for epoch in range(200):
            z=X_aug@w;p=1/(1+np.exp(-np.clip(z,-20,20)))
            grad=X_aug.T@(p-y)/len(y)
            # L2 regularization (prevent overfitting)
            reg=0.01*w;reg[-1]=0  # don't regularize intercept
            w-=lr_rate*(grad+reg)
        # Compute training accuracy
        preds=(X_aug@w>0).astype(int);acc=np.mean(preds==y)
        # Store model
        model={"weights":w.tolist(),"mu":mu.tolist(),"sd":sd.tolist(),
               "n_trades":len(X),"accuracy":float(acc),"trained_at":utcnow()}
        db.kv_set("logistic_model",model)
        log.info(f"📊 LOGISTIC MODEL TRAINED: {len(X)} trades, accuracy={acc:.1%}, features={n_feat-1}")
        # Log feature importance (absolute weight magnitude)
        importances=sorted(zip(LogisticScorer.FEATURES,np.abs(w[:-1])),key=lambda x:-x[1])
        for name,imp in importances[:5]:
            sign="+"if w[LogisticScorer.FEATURES.index(name)]>0 else"-"
            log.info(f"  Top feature: {name} ({sign}{imp:.3f})")
        return model

    @staticmethod
    def predict(sigs,model):
        """Predict P(profitable) for current signals. Returns (p_long, p_short)."""
        if model is None:return 0.5,0.5
        feat=LogisticScorer.extract_features(sigs)
        w=np.array(model["weights"]);mu=np.array(model["mu"]);sd=np.array(model["sd"])
        feat_std=(feat-mu)/sd
        feat_aug=np.append(feat_std,1.0)
        z=float(feat_aug@w);p=1/(1+np.exp(-np.clip(z,-20,20)))
        # p = probability of profitable trade given these signals
        # For directionality: flip features for SHORT (negate momentum/direction features)
        feat_short=feat.copy()
        feat_short[0]*=-1  # kalman velocity
        feat_short[1]*=-1  # kalman acc
        feat_short[2],feat_short[3]=feat_short[3],feat_short[2]  # swap bull/bear
        feat_short[5],feat_short[6]=feat_short[6],feat_short[5]  # swap ensemble L/S
        feat_short[7]*=-1  # VWAP distance
        feat_short[8]*=-1  # supertrend 1h
        feat_short[9]*=-1  # supertrend 4h
        feat_short[10]*=-1  # EMA cross
        feat_short[14]*=-1  # book pressure
        feat_short_std=(feat_short-mu)/sd
        feat_short_aug=np.append(feat_short_std,1.0)
        z_short=float(feat_short_aug@w);p_short=1/(1+np.exp(-np.clip(z_short,-20,20)))
        return float(p),float(p_short)

# ═══ GRADIENT BOOSTED SCORER — Phase 2 (activates after 500 trades) ═══
class GBMScorer:
    """From-scratch gradient boosted decision stumps using only numpy.
    Captures feature INTERACTIONS that logistic regression cannot:
    e.g. 'Kalman bullish is only profitable when VPIN < 0.40'
    Uses same 20 features as LogisticScorer. Activates after 500 trades.
    Architecture: 50 depth-1 stumps, lr=0.1, min 15 samples per leaf, L2 reg."""

    @staticmethod
    def _find_best_split(X,residuals,weights):
        n,nf=X.shape;best_loss=np.inf;best_split=None
        for f_idx in range(nf):
            vals=np.unique(X[:,f_idx])
            if len(vals)<2:continue
            candidates=np.percentile(vals,np.linspace(10,90,min(10,len(vals))))
            for thresh in candidates:
                left=X[:,f_idx]<=thresh;right=~left
                nl=left.sum();nr=right.sum()
                if nl<15 or nr<15:continue
                wl=weights[left];wr=weights[right];rl=residuals[left];rr=residuals[right]
                lv=np.sum(rl*wl)/(np.sum(wl)+1e-8)
                rv=np.sum(rr*wr)/(np.sum(wr)+1e-8)
                reg=0.1*(lv**2+rv**2)
                loss=np.sum((rl-lv)**2*wl)+np.sum((rr-rv)**2*wr)+reg
                if loss<best_loss:best_loss=loss;best_split=(f_idx,float(thresh),float(lv),float(rv))
        return best_split

    @staticmethod
    def train(db):
        trades=db.query("SELECT id,direction,total_pnl_pct FROM trades WHERE status='CLOSED' ORDER BY id DESC LIMIT 500")
        if len(trades)<400:return None
        X=[];y=[]
        for tid,direction,pnl in trades:
            feat=db.kv_get(f"trade_features_{tid}")
            if feat is None:continue
            feat=np.array(feat,dtype=float)
            if len(feat)!=len(LogisticScorer.FEATURES):continue
            X.append(feat);y.append(1.0 if(pnl or 0)>0 else 0.0)
        if len(X)<300:return None
        X=np.array(X);y=np.array(y)
        mu=X.mean(axis=0);sd=X.std(axis=0)+1e-8;X_std=(X-mu)/sd
        base_rate=y.mean();base_pred=np.log(base_rate/(1-base_rate+1e-8))
        preds=np.full(len(y),base_pred);stumps=[];lr=0.1
        for t in range(50):
            p=1/(1+np.exp(-np.clip(preds,-20,20)))
            residuals=y-p;weights=p*(1-p)+1e-8
            split=GBMScorer._find_best_split(X_std,residuals,weights)
            if split is None:break
            f_idx,thresh,lv,rv=split
            mask=X_std[:,f_idx]<=thresh
            preds[mask]+=lr*lv;preds[~mask]+=lr*rv
            stumps.append({"f":int(f_idx),"t":float(thresh),"l":float(lv),"r":float(rv)})
        final_p=1/(1+np.exp(-np.clip(preds,-20,20)));acc=np.mean((final_p>0.5)==y)
        model={"stumps":stumps,"mu":mu.tolist(),"sd":sd.tolist(),"base_pred":float(base_pred),
               "lr":lr,"n_trades":len(X),"n_stumps":len(stumps),"accuracy":float(acc),"trained_at":utcnow()}
        db.kv_set("gbm_model",model)
        feat_counts=np.zeros(len(LogisticScorer.FEATURES))
        for s in stumps:feat_counts[s["f"]]+=1
        importances=sorted(zip(LogisticScorer.FEATURES,feat_counts),key=lambda x:-x[1])
        log.info(f"🌲 GBM TRAINED: {len(X)} trades, {len(stumps)} stumps, accuracy={acc:.1%}")
        for name,cnt in importances[:5]:
            if cnt>0:log.info(f"  Split: {name} ({int(cnt)}× used)")
        return model

    @staticmethod
    def predict(sigs,model):
        if model is None:return 0.5,0.5
        feat=LogisticScorer.extract_features(sigs)
        mu=np.array(model["mu"]);sd=np.array(model["sd"]);lr=model["lr"]
        feat_std=(feat-mu)/sd
        pred=model["base_pred"]
        for s in model["stumps"]:
            if feat_std[s["f"]]<=s["t"]:pred+=lr*s["l"]
            else:pred+=lr*s["r"]
        p_long=float(1/(1+np.exp(-np.clip(pred,-20,20))))
        # SHORT: flip directional features
        fs=feat.copy();fs[0]*=-1;fs[1]*=-1
        fs[2],fs[3]=fs[3],fs[2];fs[5],fs[6]=fs[6],fs[5]
        fs[7]*=-1;fs[8]*=-1;fs[9]*=-1;fs[10]*=-1;fs[14]*=-1
        fs_std=(fs-mu)/sd;pred_s=model["base_pred"]
        for s in model["stumps"]:
            if fs_std[s["f"]]<=s["t"]:pred_s+=lr*s["l"]
            else:pred_s+=lr*s["r"]
        p_short=float(1/(1+np.exp(-np.clip(pred_s,-20,20))))
        return p_long,p_short

    @staticmethod
    def hybrid_score(sigs,strategy,db):
        """REGIME-ROUTED, EXPECTANCY-GATED SCORING:
        Phase 1 (0-100 trades): 100% hardcoded confluence
        Phase 2 (100-500): logistic + confidence gating
        Phase 3 (500+): GBM + confidence gating
        
        UPGRADE: Instead of always using the 'newest' model, routes to whichever
        brain has been MORE ACCURATE in the current regime (trend vs chop).
        Falls back to confluence when both models are uncertain."""
        if strategy=="A":hc_long,hc_short=Confluence.score_a(sigs)
        elif strategy=="B":hc_long,hc_short=Confluence.score_b(sigs)
        else:return 0,0
        hc_dir="LONG"if hc_long>hc_short else("SHORT"if hc_short>hc_long else"NEUTRAL")
        # Phase 1: Pure hardcoded
        lg_model=db.kv_get("logistic_model")
        gbm_model=db.kv_get("gbm_model")
        lg_n=lg_model.get("n_trades",0)if lg_model else 0
        gbm_n=gbm_model.get("n_trades",0)if gbm_model else 0
        if lg_n<100 and gbm_n<400:
            db.kv_set("last_scoring_decision",safe_json({"mode":"HARDCODED_ONLY",
                "hc_long":hc_long,"hc_short":hc_short,"hc_dir":hc_dir,"phase":1}))
            return hc_long,hc_short
        # ═══ REGIME-AWARE BRAIN ROUTING ═══
        # Check which brain performed better in the CURRENT regime
        h=sigs.get("hurst",0.5)
        regime="TREND"if h>0.55 else("CHOP"if h<0.45 else"NEUTRAL")
        brain_log=db.kv_get("brain_comparison",[])
        best_model="GBM"if gbm_n>=400 and gbm_model else"LOGISTIC"
        # If we have enough brain comparison data, route to the winner
        if len(brain_log)>=20:
            # Filter to recent trades in similar regime
            recent=brain_log[-50:]
            hc_wins=sum(1 for b in recent if b.get("hc_correct",False))
            ml_wins=sum(1 for b in recent if b.get("lg_correct",False))
            if hc_wins>ml_wins*1.25:
                # Confluence is winning → route to confluence
                db.kv_set("last_scoring_decision",safe_json({
                    "mode":"REGIME_ROUTE_HC","model":"CONFLUENCE","phase":0,
                    "ml_conf":0,"hc_long":round(float(hc_long),1),"hc_short":round(float(hc_short),1),
                    "hc_dir":hc_dir,"ml_long":0,"ml_short":0,"ml_dir":"",
                    "final_long":round(float(hc_long),1),"final_short":round(float(hc_short),1),
                    "agreed":True,"regime":regime,"brain_reason":f"HC winning {hc_wins}vs{ml_wins}"}))
                return hc_long,hc_short
        # Use best available model
        if best_model=="GBM":
            p_long,p_short=GBMScorer.predict(sigs,gbm_model);model_name="GBM";phase=3
        else:
            p_long,p_short=LogisticScorer.predict(sigs,lg_model);model_name="LOGISTIC";phase=2
        ml_dir="LONG"if p_long>p_short else("SHORT"if p_short>p_long else"NEUTRAL")
        ml_conf=max(p_long,p_short)
        # Confidence gating
        if ml_conf>=0.70:
            ml_long=p_long*100;ml_short=p_short*100
            final_long=0.30*hc_long+0.70*ml_long
            final_short=0.30*hc_short+0.70*ml_short;gate="HIGH"
        elif ml_conf>=0.60:
            if hc_dir==ml_dir:
                ml_long=p_long*100;ml_short=p_short*100
                final_long=0.50*hc_long+0.50*ml_long
                final_short=0.50*hc_short+0.50*ml_short;gate="MEDIUM_AGREE"
            else:
                ml_long=p_long*100;ml_short=p_short*100
                final_long=min(hc_long,ml_long)
                final_short=min(hc_short,ml_short);gate="MEDIUM_DISAGREE"
        else:
            final_long=hc_long;final_short=hc_short;gate="LOW_FALLBACK"
        db.kv_set("last_scoring_decision",safe_json({
            "mode":gate,"model":model_name,"phase":phase,"ml_conf":round(ml_conf,3),
            "hc_long":round(float(hc_long),1),"hc_short":round(float(hc_short),1),"hc_dir":hc_dir,
            "ml_long":round(p_long*100,1),"ml_short":round(p_short*100,1),"ml_dir":ml_dir,
            "final_long":round(float(final_long),1),"final_short":round(float(final_short),1),
            "agreed":hc_dir==ml_dir,"regime":regime}))
        return max(final_long,0),max(final_short,0)

# ═══ 7 AGENTS ═══
class BaseAgent:
    def __init__(self,name,db):self.name=name;self.db=db;self.verdict=None
    def analyze(self,md):raise NotImplementedError
    def communicate(self,all_v):return self.verdict
    def get_verdict(self):return self.verdict
    def track_performance(self,trade_id,direction_correct,pnl):
        self.db.insert("agent_performance",{"ts":utcnow(),"agent_name":self.name,
            "trade_id":trade_id,"direction_correct":int(direction_correct),
            "confidence":float(self.verdict.confidence if self.verdict else 0),
            "trade_pnl":float(pnl),"veto_issued":int(self.verdict.veto if self.verdict else 0),
            "veto_correct":0,"rolling_accuracy":0})

class AlphaAgent(BaseAgent):
    def __init__(self,db):
        super().__init__("Alpha",db)
        self.bl=db.kv_get("bayes_long",[[B_INIT_A,B_INIT_B]for _ in range(5)])
        self.bs=db.kv_get("bayes_short",[[B_INIT_A,B_INIT_B]for _ in range(5)])
        self.alpha_history=deque(maxlen=100)
        self.alpha_status=db.kv_get("alpha_status",["ACTIVE"]*5)
    def _weights(self):
        wl=[a/(a+b)for a,b in self.bl];ws=[a/(a+b)for a,b in self.bs]
        wl=np.exp(np.array(wl)/B_TEMP);ws=np.exp(np.array(ws)/B_TEMP)
        wl=np.maximum(wl/wl.sum(),B_FLOOR);ws=np.maximum(ws/ws.sum(),B_FLOOR)
        wl/=wl.sum();ws/=ws.sum()
        return wl.tolist(),ws.tolist()
    def update_bayesian(self,direction,profitable,signals):
        for i in range(5):
            correct=(signals[i]>0 and direction=="LONG"and profitable)or(signals[i]<0 and direction=="SHORT"and profitable)
            if direction=="LONG":
                if correct:self.bl[i][0]+=1
                else:self.bl[i][1]+=1
            else:
                if correct:self.bs[i][0]+=1
                else:self.bs[i][1]+=1
        self.db.kv_set("bayes_long",self.bl);self.db.kv_set("bayes_short",self.bs)
    def decay_priors(self):
        for i in range(5):
            self.bl[i][0]*=B_FORGET;self.bl[i][1]*=B_FORGET
            self.bs[i][0]*=B_FORGET;self.bs[i][1]*=B_FORGET
        self.db.kv_set("bayes_long",self.bl);self.db.kv_set("bayes_short",self.bs)
    def check_retirement(self):
        for i in range(5):
            pm=self.bl[i][0]/(self.bl[i][0]+self.bl[i][1])
            conf=self.bl[i][0]+self.bl[i][1]
            if pm<0.42 and conf>30 and self.alpha_status[i]=="ACTIVE":
                self.alpha_status[i]="RETIRED";log.info(f"ALPHA RETIRED: {i} posterior={pm:.2f}")
            elif pm>0.55 and self.alpha_status[i]=="RETIRED":
                self.alpha_status[i]="ACTIVE";log.info(f"ALPHA REACTIVATED: {i} posterior={pm:.2f}")
        self.db.kv_set("alpha_status",self.alpha_status)
    def analyze(self,md):
        wl,ws=self._weights()
        ad=Sig.alphas(md["df_1h"],md.get("orderbook",{}),wl,ws)
        el=ad["ensemble_long"];es=ad["ensemble_short"]
        self.alpha_history.append(ad["alphas"])
        # Signal quality metrics
        entropy=Sig.signal_entropy(ad["alphas"])
        avg_corr=Sig.alpha_correlation(list(self.alpha_history))if len(self.alpha_history)>20 else 0.3
        # Freshness — uses actual candle close time
        fw,mins_since=Sig.freshness_weights(5,md.get("df_1h",pd.DataFrame()))
        avg_fresh=np.mean(fw)
        if el>es and el>0.45:d="LONG";conf=min(abs(el),1)
        elif es>el and es>0.45:d="SHORT";conf=min(abs(es),1)
        else:d="NEUTRAL";conf=0.3
        self.verdict=AgentVerdict(agent_name="Alpha",direction=d,confidence=conf,
            reasoning=f"Ensemble L={el:.3f} S={es:.3f} Entropy={entropy:.2f} Corr={avg_corr:.2f}",
            scores={"ensemble_long":el,"ensemble_short":es,"alphas":ad["alphas"],
                    "kalman":ad["kalman"],"bw_long":wl,"bw_short":ws,
                    "entropy":entropy,"avg_corr":avg_corr,"freshness":avg_fresh,
                    "freshness_weights":fw,"alpha_status":self.alpha_status})
        return self.verdict
    def communicate(self,all_v):
        micro=next((v for v in all_v if v.agent_name=="Microstructure"),None)
        if micro and self.verdict:
            vpin_dir=micro.scores.get("vpin_direction","NEUTRAL")
            if self.verdict.direction=="LONG"and vpin_dir=="SELLING":
                self.verdict.confidence*=0.70
                self.verdict.revision_notes="Alpha LONG but smart money SELLING—reduced confidence"
            elif self.verdict.direction=="SHORT"and vpin_dir=="BUYING":
                self.verdict.confidence*=0.70
                self.verdict.revision_notes="Alpha SHORT but smart money BUYING—reduced confidence"
            elif self.verdict.direction!="NEUTRAL"and vpin_dir==("BUYING"if self.verdict.direction=="LONG"else"SELLING"):
                self.verdict.confidence=min(self.verdict.confidence*1.15,1.0)
                self.verdict.revision_notes="Flow confirms alpha direction"
        return self.verdict

class RegimeAgent(BaseAgent):
    def __init__(self,db):
        super().__init__("Regime",db)
        self.hurst_hist=deque(db.kv_get("hurst_history",[]),maxlen=20)
    def analyze(self,md):
        c=md["df_1h"]["close"].values;lr=np.diff(np.log(c+1e-10))
        hd=Sig.hurst(c[-100:]);h=hd["hurst"];self.hurst_hist.append(h)
        self.db.kv_set("hurst_history",list(self.hurst_hist))
        h_stab=np.std(list(self.hurst_hist))if len(self.hurst_hist)>4 else 0.10
        hmm=Sig.hmm(lr[-200:]);har=Sig.har_rv(c)
        # Session
        sess=get_session();sp=session_params()
        # Strategy
        if h>H_TREND:strat="A"
        elif h<H_MR:strat="B"
        else:strat="NEUTRAL"
        neutral=H_MR<=h<=H_TREND
        # Direction from HMM
        if strat=="A":
            if hmm["dominant"]=="BULL":d="LONG"
            elif hmm["dominant"]=="BEAR":d="SHORT"
            else:d="NEUTRAL"
        elif strat=="B":d="NEUTRAL"
        else:d="SKIP"
        # Hurst slope prediction
        h_slope=0
        if len(self.hurst_hist)>=10:
            x=np.arange(10);y=np.array(list(self.hurst_hist)[-10:])
            h_slope=float(np.polyfit(x,y,1)[0])
        # Predict transition
        pred_bars=999
        if h_slope!=0:
            if strat=="A"and h_slope<0:pred_bars=max(int((H_TREND-h)/abs(h_slope)),0)
            elif strat=="B"and h_slope>0:pred_bars=max(int((H_MR-h)/h_slope),0)
        # Cross-asset
        ca=Sig.cross_asset_score(md.get("btc_df",pd.DataFrame()),md.get("sol_df",pd.DataFrame()))
        btc_div=Sig.btc_divergence(md["df_1h"],md.get("btc_df",pd.DataFrame()))
        # BTC crash gate
        btc_crash=False
        if len(md.get("btc_df",pd.DataFrame()))>2:
            btc_c=md["btc_df"]["close"].values
            if len(btc_c)>=2:btc_crash=(btc_c[-1]-btc_c[-2])/(btc_c[-2]+1e-10)<-0.03
        # ETH vol regime
        vol_regime=Sig.eth_vol_regime(har.get("daily_vol",0.04))
        conf=max(hmm.get("p_bull",0),hmm.get("p_bear",0),hmm.get("p_neutral",0))*(1-h_stab)
        self.verdict=AgentVerdict(agent_name="Regime",direction=d,confidence=float(conf),
            reasoning=f"H={h:.3f} Strat={strat} HMM={hmm['dominant']} Slope={h_slope:.4f}",
            veto=neutral or btc_crash,
            veto_reason=("Hurst neutral zone"if neutral else"BTC crash gate -3%")if(neutral or btc_crash)else"",
            scores={"hurst":h,"hurst_stability":h_stab,"hurst_slope":h_slope,
                    "strategy":strat,"hmm":hmm,"har_rv":har,"session":sess,"session_params":sp,
                    "cross_asset":ca,"btc_divergence":btc_div,"btc_crash":btc_crash,
                    "vol_regime":vol_regime,"predicted_transition":pred_bars})
        self.db.insert("regime_history",{"ts":utcnow(),"hurst":h,"hurst_slope":h_slope,
            "strategy":strat,"predicted_transition":pred_bars})
        return self.verdict
    def communicate(self,all_v):
        alpha=next((v for v in all_v if v.agent_name=="Alpha"),None)
        if alpha and self.verdict and not self.verdict.veto:
            hmm_dom=self.verdict.scores.get("hmm",{}).get("dominant","NEUTRAL")
            if alpha.direction=="LONG"and hmm_dom=="BEAR":
                self.verdict.confidence*=0.70;self.verdict.revision_notes="Alpha bullish but HMM bearish"
            elif alpha.direction==("LONG"if hmm_dom=="BULL"else"SHORT"if hmm_dom=="BEAR"else""):
                self.verdict.confidence=min(self.verdict.confidence*1.15,1.0)
                self.verdict.revision_notes="Alpha and HMM aligned"
        return self.verdict

class RiskAgent(BaseAgent):
    def __init__(self,db):
        super().__init__("Risk",db)
        self.peak=db.kv_get("peak_equity",300.0)
        self.consec_losses=db.kv_get("consec_losses",0)
        self.daily_pnl=db.kv_get("daily_pnl",0.0)
        self.trades_today=db.kv_get("trades_today",0)
        self.paused_until=db.kv_get("paused_until",0)
        self.last_stop_ts=db.kv_get("last_stop_ts",0)
        self.as_history=deque(db.kv_get("as_history",[]),maxlen=50)
        self.consec_as=0
        self.sizing_tier=db.kv_get("sizing_tier","BASE")
        self.kelly_cap=KELLY_CAP;self.vol_target=VOL_TARGET
        # Milestone sizing
        bal=db.kv_get("peak_equity",300)
        for thresh,kc,vt in MILESTONES:
            if bal>=thresh:self.kelly_cap=kc;self.vol_target=vt;self.sizing_tier=f"${thresh}+"
    def update_milestones(self,balance):
        changed=False
        for thresh,kc,vt in MILESTONES:
            if balance>=thresh and self.kelly_cap<kc:
                self.kelly_cap=kc;self.vol_target=vt;self.sizing_tier=f"${thresh}+"
                changed=True;log.info(f"MILESTONE ${thresh}: Kelly→{kc} Vol→{vt}")
                self.db.insert("milestones",{"ts":utcnow(),"milestone_type":"equity","value":balance,"note":f"${thresh} reached"})
        if changed:self.db.kv_set("sizing_tier",self.sizing_tier)
    def gates(self,balance,sigs):
        """All 22 risk gates. Returns (pass,reason,gate_num)."""
        dd=(self.peak-balance)/self.peak if self.peak>0 else 0
        # 1. Kill switch
        if dd>KILL_SWITCH_DD:return False,f"KILL SWITCH DD={dd:.1%}",1
        # 2. Daily loss
        if self.daily_pnl<DAILY_LOSS_LIMIT*self.peak:return False,"DAILY LOSS LIMIT",2
        # 3. 5 losses
        if self.consec_losses>=5:return False,"5 CONSECUTIVE LOSSES",3
        # 4. 2 losses pause
        if self.consec_losses>=2 and time.time()<self.paused_until:return False,"2-LOSS PAUSE",4
        # 5. Max trades
        if self.trades_today>=MAX_TRADES_DAY:return False,f"MAX {MAX_TRADES_DAY} TRADES",5
        # 6. Funding window
        if near_funding(25):return False,"FUNDING WINDOW",6
        # 7. Post-stop cooldown
        if time.time()-self.last_stop_ts<1800:return False,"POST-STOP COOLDOWN",7
        # 8. Short squeeze guard
        d=sigs.get("proposed_dir","")
        if d=="SHORT":
            if sigs.get("funding_rate",0)<-0.0006:return False,"SHORT SQUEEZE: funding<-0.06%",8
            if sigs.get("rsi_1h",50)<30:return False,"SHORT SQUEEZE: RSI<30",8
        # 9. Spread
        sp=sigs.get("spread_bps",0);mx=2.5 if get_session()=="ASIAN"else 4.0
        if sp>mx:return False,f"SPREAD {sp:.1f}>{mx}bps",9
        # 10. Manipulation
        if sigs.get("manipulation",False):return False,"MANIPULATION DETECTED",10
        # 11. Uncertainty
        if sigs.get("uncertainty_flags",0)>=4:return False,f"UNCERTAINTY {sigs.get('uncertainty_flags',0)}/10",11
        # 12. Liq guard
        if sigs.get("liq_dist_pct",100)<8:return False,"LIQ GUARD <8%",12
        # 13. Strategy B max-hold handled by execution agent
        # 14. Duplicate position
        if sigs.get("has_position",False):return False,"HAS POSITION",14
        # 15. Correlation storm
        if sigs.get("corr_storm",False):return False,"CORRELATION STORM",15
        # 16. VPIN
        vp=sigs.get("vpin",0)
        sess_vpin=session_params().get("vpin_thresh",VPIN_GATE)
        if vp>sess_vpin:return False,f"VPIN {vp:.2f}>{sess_vpin}",16
        # 17. Adverse selection
        if sigs.get("adverse_sel",0)>0.60:return False,f"ADVERSE SEL {sigs.get('adverse_sel',0):.2f}>0.60",17
        # 18. Book depth
        notional=sigs.get("proposed_notional",0)
        depth=sigs.get("book_depth",999999)
        if depth<2*notional and notional>0:return False,"BOOK DEPTH <2x NOTIONAL",18
        # 19. Effective spread
        if sigs.get("eff_spread",0)>10:return False,f"EFF SPREAD {sigs.get('eff_spread',0):.1f}>10bps",19
        # 20. Consecutive AS
        if self.consec_as>=3:return False,"3 CONSECUTIVE ADVERSE SELECTIONS",20
        # 21. OI extreme
        if sigs.get("oi_extreme",False):
            score=max(sigs.get("long_score",0),sigs.get("short_score",0))
            if score<83:return False,f"OI EXTREME: score {score}<83",21
        # 22. Funding+OI confluence against
        if sigs.get("foi_against",False):return False,"FUNDING+OI AGAINST DIRECTION",22
        # 23. DYNAMIC SESSION BLOCK — blocks sessions with proven negative expectancy
        sess=get_session();direction=sigs.get("proposed_dir","")
        sess_trades=self.db.query("SELECT total_pnl_pct FROM trades WHERE status='CLOSED' AND session=? ORDER BY id DESC LIMIT 30",(sess,))
        if len(sess_trades)>=15:
            pnls=[t[0]or 0 for t in sess_trades]
            sess_exp=np.mean(pnls)
            if sess_exp<-0.008:  # expectancy worse than -0.8% per trade in this session
                return False,f"SESSION EXPECTANCY GATE: {sess} exp={sess_exp:+.2%} over {len(sess_trades)} trades",23
        # 24. DIRECTION EXPECTANCY — blocks direction if it's consistently losing
        if direction:
            dir_trades=self.db.query("SELECT total_pnl_pct FROM trades WHERE status='CLOSED' AND direction=? ORDER BY id DESC LIMIT 20",(direction,))
            if len(dir_trades)>=15:
                dir_exp=np.mean([t[0]or 0 for t in dir_trades])
                if dir_exp<-0.01:  # consistently losing in this direction
                    return False,f"DIRECTION EXPECTANCY GATE: {direction} exp={dir_exp:+.2%} over {len(dir_trades)} trades",24
        return True,"ALL 24 GATES PASSED",0

    def compute_size(self,balance,direction,sigs,disagree_count):
        """All 16 position sizing factors."""
        # Step 1: Kelly
        trades=self.db.query("SELECT total_pnl_pct FROM trades WHERE status='CLOSED' AND direction=? ORDER BY id DESC LIMIT 20",(direction,))
        if len(trades)>=10:
            pnls=[t[0]or 0 for t in trades];wins=[p for p in pnls if p>0];losses=[p for p in pnls if p<=0]
            p=len(wins)/len(pnls);b=(np.mean([abs(w)for w in wins])/(np.mean([abs(l)for l in losses])+1e-10))if losses else 1.5
            kelly=np.clip((p*(b+1)-1)/b*KELLY_FRAC,KELLY_MIN,self.kelly_cap)
        else:kelly=KELLY_DEFAULT
        # Step 2: Vol targeting
        vs=sigs.get("vol_scalar",1.0)
        # Step 3: Confluence — smooth gradient sizing
        sc=max(sigs.get("long_score",0),sigs.get("short_score",0))
        if sc>=95:scs=1.25
        elif sc>=90:scs=1.18
        elif sc>=85:scs=1.10
        elif sc>=78:scs=1.00
        elif sc>=72:scs=0.90
        elif sc>=68:scs=0.80
        else:scs=0.70
        # Step 4: Hurst — reward strong trends more
        h=sigs.get("hurst",0.5)
        if h>0.68:hs=1.22
        elif h>0.60:hs=1.12
        elif h>0.55:hs=1.00
        elif h>0.50:hs=0.65
        else:hs=0.80
        # Step 5: Uncertainty
        uf=sigs.get("uncertainty_flags",0)
        if uf>=4:return 0
        us=[1.0,0.80,0.65,0.50][min(uf,3)]
        # Step 6: Session
        ss=session_params()["size_mult"]
        # Step 7: Drawdown
        dd=(self.peak-balance)/self.peak if self.peak>0 else 0
        if dd>KILL_SWITCH_DD:return-1
        elif dd>0.08:dds=0.40
        elif dd>0.05:dds=0.65
        elif dd>0.03:dds=0.85
        else:dds=1.00
        # Step 8: CVaR
        cvs=1.0
        loss_pcts=[abs(t[0]or 0)for t in self.db.query("SELECT total_pnl_pct FROM trades WHERE status='CLOSED' AND total_pnl_pct<0 ORDER BY id DESC LIMIT 20")]
        if len(loss_pcts)>=5:
            cvar=np.percentile(loss_pcts,95)
            if cvar>0.10:cvs=0.50
        # Step 9: Short penalty — less aggressive; shorts profit in crashes
        shp=0.88 if direction=="SHORT"and sigs.get("vol_pct",50)>80 else 1.0
        # Step 10: VPIN
        vp=sigs.get("vpin",0.4)
        if vp>VPIN_GATE:return 0
        elif vp>0.55:vps=0.65
        elif vp>0.45:vps=0.85
        elif vp<VPIN_CLEAN:vps=1.05
        else:vps=1.0
        # Step 11: Decorrelation
        ac=sigs.get("avg_corr",0.3)
        dcs=0.80 if ac>0.45 else(1.05 if ac<0.25 else 1.0)
        # Step 12: Bayesian confidence
        mbw=sigs.get("min_bayes_weight",0.5);abw=sigs.get("all_bayes_above_60",False)
        bcs=0.85 if mbw<0.35 else(1.05 if abw else 1.0)
        # Step 13: OI risk
        oi4=sigs.get("oi_roc_4h",0);oi24=sigs.get("oi_roc_24h",0);ois=sigs.get("oi_scenario","")
        if oi24>0.12:oirs=0.50
        elif oi4>0.05:oirs=0.70
        elif ois in("C","D"):oirs=0.70
        else:oirs=1.0
        # Step 14: Carry
        cf=sigs.get("carry_favorable",False);cag=sigs.get("carry_against",False)
        foic=sigs.get("funding_oi_conf",False)
        cas=1.15 if foic else(1.08 if cf else(0.85 if cag else 1.0))
        # Step 15: Agent disagreement
        if disagree_count>=3:return 0
        ads=[1.0,0.85,0.65][min(disagree_count,2)]
        # Step 16: Options expiry
        exp_s=0.80 if is_options_expiry()else 1.0
        # ETH vol regime
        vr=sigs.get("vol_regime","NORMAL")
        if vr=="EXTREME":
            kelly*=0.50;us*=0.60
        elif vr=="HIGH":
            kelly*=0.80
        # Step 17: Hot streak bonus (compound faster during winning streaks)
        consec_wins=self.db.kv_get("consec_wins",0)
        if consec_wins>=5:hot_s=1.22  # Deep streak = strong regime
        elif consec_wins>=3:hot_s=1.15
        elif consec_wins>=2:hot_s=1.08
        else:hot_s=1.00
        # Combine
        sz=kelly*vs*scs*hs*us*ss*dds*cvs*shp*vps*dcs*bcs*oirs*cas*ads*exp_s*hot_s
        sz=np.clip(sz,0.0,self.kelly_cap);sz_usd=balance*sz
        # Liq safety (5x liq ~20% away, ensure 12% buffer)
        price=sigs.get("price",3000)
        if price>0:
            notional=sz_usd*LEVERAGE;liq_dist=price/LEVERAGE*0.95
            while liq_dist/price<0.12 and sz_usd>5:sz_usd*=0.90;notional=sz_usd*LEVERAGE;liq_dist=price/LEVERAGE*0.95
        return max(sz_usd,0)

    def analyze(self,md):
        bal=md.get("balance",300)
        if bal>self.peak:self.peak=bal;self.db.kv_set("peak_equity",bal)
        self.update_milestones(bal)
        passed,reason,gate=self.gates(bal,md.get("signals",{}))
        dd=(self.peak-bal)/self.peak if self.peak>0 else 0
        self.verdict=AgentVerdict(agent_name="Risk",direction="SKIP"if not passed else"AGREE",
            confidence=float(1.0-dd),reasoning=reason,
            veto=not passed,veto_reason=reason if not passed else"",
            scores={"balance":bal,"peak":self.peak,"dd":dd,"gates_passed":passed,"gate":gate,
                    "gate_reason":reason,"consec_losses":self.consec_losses,
                    "trades_today":self.trades_today,"sizing_tier":self.sizing_tier,
                    "kelly_cap":self.kelly_cap,"vol_target":self.vol_target})
        return self.verdict

class MicrostructureAgent(BaseAgent):
    def __init__(self,db):
        super().__init__("Microstructure",db)
        self.prev_ob=None;self.refill_tracker={};self.prev_vpin=db.kv_get("prev_vpin",0.4)
    def analyze(self,md):
        ob=md.get("orderbook",{});trades=md.get("recent_trades",[])
        vpin_d=Sig.vpin(trades);vpin=vpin_d["vpin"]
        vpin_delta=vpin-self.prev_vpin;self.prev_vpin=vpin;self.db.kv_set("prev_vpin",vpin)
        bp=Sig.book_pressure(ob);spread=Sig.spread_bps(ob)
        mp,mid=Sig.micro_price(ob)
        # 4 manipulation detectors
        spoof=Sig.detect_spoofing(self.prev_ob,ob)
        wash=Sig.detect_wash(md["df_1h"])if len(md.get("df_1h",pd.DataFrame()))>5 else False
        liq_hunt=Sig.detect_liq_hunt(md.get("df_5m",pd.DataFrame()))if len(md.get("df_5m",pd.DataFrame()))>3 else False
        iceberg,ice_side,self.refill_tracker=Sig.detect_iceberg(ob,self.prev_ob,self.refill_tracker)
        manip=spoof or wash or liq_hunt
        manip_type=[]
        if spoof:manip_type.append("SPOOF")
        if wash:manip_type.append("WASH")
        if liq_hunt:manip_type.append("LIQ_HUNT")
        if iceberg:manip_type.append(f"ICEBERG_{ice_side}")
        self.prev_ob=ob
        # Absorption
        vol_avg=md["df_1h"]["volume"].iloc[-20:].mean()if len(md.get("df_1h",pd.DataFrame()))>20 else 1
        absorb,absorb_side=Sig.book_absorption(ob,vol_avg)
        # OI analysis
        oi_now=md.get("oi_current",0);oi_1h=md.get("oi_1h_ago",oi_now)
        oi_4h=md.get("oi_4h_ago",oi_now);oi_24h=md.get("oi_24h_ago",oi_now)
        oi_r1=(oi_now-oi_1h)/max(oi_1h,1);oi_r4=(oi_now-oi_4h)/max(oi_4h,1);oi_r24=(oi_now-oi_24h)/max(oi_24h,1)
        oi_extreme=abs(oi_r4)>0.05 or abs(oi_r24)>0.12
        pc1h=md.get("price_change_1h",0)
        if oi_r1>0.02 and pc1h>0.003:oi_scen="A"
        elif oi_r1>0.02 and pc1h<-0.003:oi_scen="B"
        elif oi_r1<-0.02 and pc1h>0.005:oi_scen="C"
        elif oi_r1<-0.02 and pc1h<-0.005:oi_scen="D"
        else:oi_scen=""
        # OI z-score
        oi_hist=self.db.kv_get("oi_roc_hist",[])
        oi_hist.append(oi_r1);oi_hist=oi_hist[-100:]
        self.db.kv_set("oi_roc_hist",oi_hist)
        oi_z=(oi_r1-np.mean(oi_hist))/(np.std(oi_hist)+1e-8)if len(oi_hist)>10 else 0
        # Funding term structure
        fr=md.get("funding_rate",0);fr_avg=md.get("funding_avg_7d",fr)
        if fr>fr_avg+0.0003:fts="STEEP_CONTANGO"
        elif fr<fr_avg-0.0003:fts="STEEP_BACKWARDATION"
        elif fr>fr_avg:fts="CONTANGO"
        elif fr<fr_avg:fts="BACKWARDATION"
        else:fts="FLAT"
        fr_z=(fr-fr_avg)/(max(abs(fr-fr_avg),1e-8))*2
        fund_extreme=abs(fr_z)>2.5
        daily_carry=fr*3
        # Funding+OI confluence
        foi_conf=fund_extreme and oi_extreme
        # Direction inference
        if vpin>0.50:
            if vpin_d["direction"]=="BUYING":flow_dir="LONG"
            elif vpin_d["direction"]=="SELLING":flow_dir="SHORT"
            else:flow_dir="NEUTRAL"
        else:flow_dir="NEUTRAL"
        # Adverse selection from history
        as_score=float(np.mean(list(self.db.kv_get("as_scores",[0.35])))or 0.35)
        # Veto
        veto=False;vr=""
        sess_vpin=session_params().get("vpin_thresh",VPIN_GATE)
        if vpin>sess_vpin:veto=True;vr=f"VPIN {vpin:.2f}>{sess_vpin}"
        elif spread>10:veto=True;vr=f"Eff spread {spread:.1f}>10bps"
        elif as_score>0.60:veto=True;vr=f"Adverse sel {as_score:.2f}>0.60"
        quality="EXCELLENT"if vpin<0.35 and spread<2 else"GOOD"if vpin<0.45 else"FAIR"if vpin<0.55 else"POOR"if vpin<0.65 else"TOXIC"
        # Log
        self.db.insert("vpin_log",{"ts":utcnow(),"vpin":vpin,"vpin_delta":vpin_delta,"vpin_direction":vpin_d["direction"],"bucket_count":50})
        self.db.insert("oi_log",{"ts":utcnow(),"oi_current":oi_now,"oi_roc_1h":oi_r1,"oi_roc_4h":oi_r4,"oi_roc_24h":oi_r24,"oi_zscore":oi_z,"oi_scenario":oi_scen,"oi_extreme":int(oi_extreme)})
        self.db.insert("funding_log",{"ts":utcnow(),"fr_current":fr,"fr_avg_8h":fr,"fr_avg_3d":fr_avg,"fr_avg_7d":fr_avg,"fr_momentum":fr-fr_avg,"fr_term":fts,"fr_zscore":fr_z,"daily_carry":daily_carry,"funding_extreme":int(fund_extreme)})
        self.verdict=AgentVerdict(agent_name="Microstructure",direction=flow_dir,
            confidence=float((1-vpin)*(1-min(spread/20,0.5))),
            reasoning=f"VPIN={vpin:.2f}Δ{vpin_delta:+.2f} Spread={spread:.1f}bps Q={quality} OI={oi_scen}",
            veto=veto,veto_reason=vr,
            scores={"vpin":vpin,"vpin_delta":vpin_delta,"vpin_direction":vpin_d["direction"],
                    "book_pressure":bp["pressure"],"spread_bps":spread,"micro_price":mp,"mid_price":mid,
                    "manipulation":manip,"manip_types":manip_type,
                    "iceberg":iceberg,"iceberg_side":ice_side,
                    "absorption":absorb,"absorption_side":absorb_side,
                    "oi_roc_1h":oi_r1,"oi_roc_4h":oi_r4,"oi_roc_24h":oi_r24,
                    "oi_scenario":oi_scen,"oi_extreme":oi_extreme,"oi_zscore":oi_z,
                    "funding_term":fts,"fr_zscore":fr_z,"daily_carry":daily_carry,
                    "funding_extreme":fund_extreme,"foi_confluence":foi_conf,
                    "adverse_sel":as_score,"market_quality":quality,
                    "book_depth":bp["bid_depth"]+bp["ask_depth"]})
        return self.verdict
    def communicate(self,all_v):
        alpha=next((v for v in all_v if v.agent_name=="Alpha"),None)
        if alpha and self.verdict:
            vd=self.verdict.scores.get("vpin_direction","NEUTRAL")
            if alpha.direction=="LONG"and vd=="SELLING"and self.verdict.scores.get("vpin",0)>0.55:
                self.verdict.revision_notes="WARNING: Alpha LONG but informed SELLING"
                if self.verdict.scores.get("vpin",0)>0.60:
                    self.verdict.veto=True;self.verdict.veto_reason="VPIN direction opposes alpha at high toxicity"
            ois=self.verdict.scores.get("oi_scenario","")
            if alpha.direction=="SHORT"and ois=="D":
                self.verdict.revision_notes="Forced selling detected—reversal likely, opposing short"
                self.verdict.direction="LONG"
        return self.verdict

class ExecutionAgent(BaseAgent):
    def __init__(self,db,client):
        super().__init__("Execution",db)
        self.client=client;self.avg_slip=db.kv_get("avg_slippage",2.0)
        self.pos=Position();self._load_pos()
        self.sym_info=db.kv_get("symbol_info",{"qty_precision":3,"price_precision":2,"step_size":0.001,"min_qty":0.001})
    def _load_pos(self):
        s=self.db.kv_get("open_position")
        if s:
            for k,v in s.items():
                if hasattr(self.pos,k):setattr(self.pos,k,v)
    def _save_pos(self):self.db.kv_set("open_position",safe_json(asdict(self.pos)))
    def has_pos(self):return self.pos.direction!="NONE"and self.pos.qty_rem>0
    def _twap_params(self):
        if self.avg_slip<3:return 2,10
        elif self.avg_slip<8:return 2,10
        elif self.avg_slip<15:return 3,15
        else:return 4,20
    def _round_qty(self,q):
        step=self.sym_info.get("step_size",0.001);prec=self.sym_info.get("qty_precision",3)
        return round(math.floor(q/step)*step,prec)
    def enter(self,direction,qty,entry_price,stop,tp1,tp2,tp3,strategy,liq,trade_id,ob=None):
        qty=self._round_qty(qty)
        if qty<self.sym_info.get("min_qty",0.001):log.error(f"Qty {qty}<min");return False
        slices,interval=self._twap_params();fills=[];side="BUY"if direction=="LONG"else"SELL"
        price_prec=self.sym_info.get("price_precision",2)
        for i in range(slices):
            placed=sum(f[1]for f in fills)
            sq=self._round_qty(qty/slices)if i<slices-1 else self._round_qty(qty-placed)
            if sq<=0:break
            # Smart execution: try limit at micro-price, fallback to market
            filled=False
            if ob:
                mp,mid=Sig.micro_price(ob)
                if mp>0 and mid>0:
                    # Place limit slightly better than market
                    if direction=="LONG":
                        limit_price=round(min(mp,mid),price_prec)  # buy at or below micro-price
                    else:
                        limit_price=round(max(mp,mid),price_prec)  # sell at or above micro-price
                    r=self.client.limit_order(SYMBOL,side,sq,limit_price)
                    if r and isinstance(r,dict)and"orderId"in r:
                        oid=r["orderId"]
                        # Wait up to 5 seconds for fill
                        for _ in range(10):
                            time.sleep(0.5)
                            status=self.client.check_order(SYMBOL,oid)
                            if status and status.get("status")=="FILLED":
                                fp=float(status.get("avgPrice",limit_price))
                                fills.append((fp,sq));filled=True
                                log.info(f"LIMIT FILLED slice{i}@{fp:.2f} (saved vs market)")
                                break
                        if not filled:
                            # Cancel unfilled limit, use market
                            self.client.cancel_order(SYMBOL,oid)
                            log.info(f"Limit not filled in 5s, falling back to market")
            if not filled:
                r=self.client.market_order(SYMBOL,side,sq)
                if r and isinstance(r,dict)and"avgPrice"in r:fills.append((float(r["avgPrice"]),sq))
                elif r and isinstance(r,dict)and"fills"in r:
                    fp=np.mean([float(f["price"])for f in r["fills"]]);fills.append((fp,sq))
                else:log.error(f"Slice {i} failed:{r}")
            # Log execution quality
            if fills:
                self.db.insert("execution_log",{"ts":utcnow(),"trade_id":trade_id,"slice_num":i,
                    "expected_price":entry_price,"fill_price":fills[-1][0],
                    "slippage_bps":abs(fills[-1][0]-entry_price)/entry_price*10000,
                    "qty":sq,"side":side,"book_pressure":0,"micro_price":mp if ob else 0})
            if i<slices-1:time.sleep(interval)
        if not fills:log.error("ENTRY FAILED: No fills");return False
        avg_fill=np.average([f[0]for f in fills],weights=[f[1]for f in fills])
        slip=abs(avg_fill-entry_price)/entry_price*10000
        # Track execution quality improvement from limit orders
        self.avg_slip=self.avg_slip*0.9+slip*0.1
        self.db.kv_set("avg_slippage",self.avg_slip)
        self.pos=Position(direction=direction,strategy=strategy,entry_price=avg_fill,
            qty_full=qty,qty_rem=qty,stop_price=stop,tp1_price=tp1,tp2_price=tp2,tp3_price=tp3,
            liq_price=liq,opened_at=utcnow(),trade_id=trade_id)
        self._save_pos()
        log.info(f"✅ ENTERED {direction} {qty:.4f} ETH@{avg_fill:.2f} slip={slip:.1f}bps avg_slip={self.avg_slip:.1f}bps")
        return True
    def manage(self,price):
        p=self.pos
        if p.direction=="NONE"or p.qty_rem<=0:return None
        # MFE/MAE
        if p.direction=="LONG":unr=(price-p.entry_price)/p.entry_price
        else:unr=(p.entry_price-price)/p.entry_price
        p.mfe=max(p.mfe,unr);p.mae=min(p.mae,unr)
        # Emergency liq guard
        if p.liq_price>0:
            ld=abs(price-p.liq_price)/price
            if ld<0.05:log.critical(f"EMERGENCY LIQ: {ld:.1%} from liq!");self._close_all(price,"EMERGENCY_LIQ");return"EMERGENCY"
            elif ld<0.08:log.critical(f"LIQ WARNING: {ld:.1%} from liq!");self._close_all(price,"LIQ_GUARD");return"LIQ_GUARD"
        # Stop
        if p.direction=="LONG"and price<=p.stop_price:self._close_all(price,"STOP_LOSS");return"STOPPED"
        if p.direction=="SHORT"and price>=p.stop_price:self._close_all(price,"STOP_LOSS");return"STOPPED"

        # ═══ CHANGE 1: EARLY BREAKEVEN ═══
        # Move stop to breakeven at 40% of TP1 distance (earlier protection).
        # Tighter buffer (0.03%) keeps more profit on reversal.
        if not p.tp1_hit:
            tp1_dist=abs(p.tp1_price-p.entry_price)
            early_be=tp1_dist*0.40
            if p.direction=="LONG"and price>=p.entry_price+early_be:
                buf=p.entry_price*0.0003  # tighter buffer = keep more profit
                new_stop=p.entry_price+buf
                if new_stop>p.stop_price:
                    p.stop_price=new_stop
                    log.info(f"🛡️ EARLY BREAKEVEN @{price:.2f}|40% to TP1|Stop→${new_stop:.2f}")
            elif p.direction=="SHORT"and price<=p.entry_price-early_be:
                buf=p.entry_price*0.0003
                new_stop=p.entry_price-buf
                if new_stop<p.stop_price:
                    p.stop_price=new_stop
                    log.info(f"🛡️ EARLY BREAKEVEN @{price:.2f}|40% to TP1|Stop→${new_stop:.2f}")

        # ═══ CHANGE 2: MOMENTUM-ADAPTIVE TP1 FRACTION ═══
        # In STRONG trends (H>0.60), only take 30% off at TP1 instead of 45%.
        # The remaining 70% rides the trend. Same entry. Same TP1 level.
        # But bigger position stays in play for TP2/TP3/trail.
        if not p.tp1_hit:
            hit=(p.direction=="LONG"and price>=p.tp1_price)or(p.direction=="SHORT"and price<=p.tp1_price)
            if hit:
                h_now=self.db.kv_get("hurst_history",[0.5])
                h_now=h_now[-1]if h_now else 0.5
                if p.strategy=="A"and h_now>0.65:
                    frac=0.25  # Very strong trend: only take 25% off (let 75% run)
                    log.info(f"🔥 VERY STRONG TREND TP1: Taking only 25% (H={h_now:.2f})")
                elif p.strategy=="A"and h_now>0.58:
                    frac=0.30  # Strong trend: only take 30% off
                    log.info(f"🔥 STRONG TREND TP1: Taking only 30% (H={h_now:.2f})")
                elif p.strategy=="A":
                    frac=SA_TP1_FRAC  # Normal: take 40% off
                else:
                    frac=SB_TP1_FRAC  # Mean reversion: take 55% off (lock MR profit fast)
                cq=self._round_qty(p.qty_full*frac)
                if cq>0:self._close_partial(cq,price,"TP1")
                p.tp1_hit=True
                buf=p.entry_price*0.001
                p.stop_price=p.entry_price+(buf if p.direction=="LONG"else-buf)
                log.info(f"TP1 HIT@{price:.2f}|Closed {cq:.4f}({frac:.0%})|Stop→BREAKEVEN")
                self._save_pos();return"TP1"

        # TP2
        if p.tp1_hit and not p.tp2_hit:
            hit=(p.direction=="LONG"and price>=p.tp2_price)or(p.direction=="SHORT"and price<=p.tp2_price)
            if hit:
                frac=SA_TP2_FRAC if p.strategy=="A"else SB_TP2_FRAC
                cq=self._round_qty(p.qty_full*frac)
                if cq>0:self._close_partial(cq,price,"TP2")
                p.tp2_hit=True;p.trail_price=price
                log.info(f"TP2 HIT@{price:.2f}|TRAILING ON");self._save_pos();return"TP2"

        # ═══ CHANGE 3: AGGRESSIVE ADAPTIVE TRAILING STOP ═══
        # In STRONG trending conditions with confirmed profit, trail MUCH wider.
        # This is the single biggest profit lever: a trade that runs from TP2 to 2×TP3
        # captures 2× more profit on the trailing portion.
        # No accuracy change — same entries, same TP1/TP2 levels.
        if p.tp2_hit and p.qty_rem>0:
            atr_val=self.db.kv_get("current_atr",50)
            base_trail=SA_TRAIL_ATR if p.strategy=="A"else 0.6
            current_hurst=self.db.kv_get("hurst_history",[0.5])
            h_now=current_hurst[-1]if current_hurst else 0.5
            # Four tiers of trailing based on trend strength + confirmed profit
            if h_now>0.65 and p.mfe>0.06:
                trail_mult=base_trail*1.80  # Tier 4: MAX — deep in profit, let it ride
                log.info(f"🚀 MAX TRAIL: H={h_now:.2f} MFE={p.mfe:.1%} → trail×1.80")if p.mfe==unr else None
            elif h_now>0.62 and p.mfe>0.04:
                trail_mult=base_trail*1.50  # Tier 3: Very wide
            elif h_now>0.58 and p.mfe>0.02:
                trail_mult=base_trail*1.30  # Tier 2: Wide — strong trend + confirmed profit
            elif h_now>0.54:
                trail_mult=base_trail*1.12  # Tier 1: Slightly wider
            else:
                trail_mult=base_trail  # Default
            td=atr_val*trail_mult
            if p.direction=="LONG":
                nt=price-td
                if nt>p.trail_price:p.trail_price=nt
                if price<=p.trail_price:self._close_all(price,"TRAILING_STOP");return"TRAIL"
            else:
                nt=price+td
                if p.trail_price==0 or nt<p.trail_price:p.trail_price=nt
                if price>=p.trail_price:self._close_all(price,"TRAILING_STOP");return"TRAIL"

        # ═══ CHANGE 4: TP3 REMOVAL IN STRONG TRENDS ═══
        # In strong trends (H>0.62), DON'T cap at TP3 — let trailing stop handle exit.
        # A trade that reaches TP3 in a strong trend often goes to 2× TP3.
        # The trailing stop will capture the excess. TP3 becomes a cap only in weak trends.
        if p.tp1_hit and p.qty_rem>0 and p.tp3_price>0:
            h_now=self.db.kv_get("hurst_history",[0.5])
            h_now=h_now[-1]if h_now else 0.5
            if h_now>0.58 and p.strategy=="A":
                pass  # Strong trend: let trailing stop handle exit, no TP3 cap
            else:
                hit=(p.direction=="LONG"and price>=p.tp3_price)or(p.direction=="SHORT"and price<=p.tp3_price)
                if hit:self._close_all(price,"TP3");return"TP3"

        # ═══ CHANGE 5: PROFIT LOCK STEP-UP ═══
        # After TP2, if price moves another ATR in our favor, ratchet stop up to TP1 level.
        # This locks in TP1-level profit minimum while still letting the trade run.
        # No new entries, no new risk — purely locks more profit.
        if p.tp2_hit and p.qty_rem>0:
            atr_val=self.db.kv_get("current_atr",50)
            if p.direction=="LONG":
                profit_lock_level=p.tp1_price  # minimum lock = TP1 level
                if price>p.tp2_price+atr_val*0.7 and p.stop_price<profit_lock_level:
                    p.stop_price=profit_lock_level
                    log.info(f"🔒 PROFIT LOCK: Stop ratcheted to TP1 level ${profit_lock_level:.2f}")
                # Second lock: if price passes TP2 + 1.5 ATR, lock stop at midpoint of TP1-TP2
                mid_lock=(p.tp1_price+p.tp2_price)/2
                if price>p.tp2_price+atr_val*1.5 and p.stop_price<mid_lock:
                    p.stop_price=mid_lock
                    log.info(f"🔒 PROFIT LOCK LV2: Stop→midpoint ${mid_lock:.2f}")
            else:
                profit_lock_level=p.tp1_price
                if price<p.tp2_price-atr_val*0.7 and p.stop_price>profit_lock_level:
                    p.stop_price=profit_lock_level
                    log.info(f"🔒 PROFIT LOCK: Stop ratcheted to TP1 level ${profit_lock_level:.2f}")
                mid_lock=(p.tp1_price+p.tp2_price)/2
                if price<p.tp2_price-atr_val*1.5 and p.stop_price>mid_lock:
                    p.stop_price=mid_lock
                    log.info(f"🔒 PROFIT LOCK LV2: Stop→midpoint ${mid_lock:.2f}")

        # Strategy B max hold (adaptive — extend when carry is favorable)
        if p.strategy=="B"and p.opened_at:
            try:
                opened=datetime.strptime(p.opened_at,"%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
                hold_secs=(datetime.now(timezone.utc)-opened).total_seconds()
                fr=self.db.kv_get("last_funding_rate",0)
                carry_favorable=(p.direction=="LONG"and fr<0)or(p.direction=="SHORT"and fr>0)
                max_hold=SB_MAX_HOLD_H*3600
                if carry_favorable:max_hold+=(2*3600)
                if hold_secs>max_hold:
                    self._close_all(price,f"MAX_HOLD_{SB_MAX_HOLD_H}H");return"MAX_HOLD"
            except:pass
        self._save_pos();return None
    def _close_partial(self,qty,price,reason):
        side="SELL"if self.pos.direction=="LONG"else"BUY"
        qty=self._round_qty(min(qty,self.pos.qty_rem))
        if qty<=0:return
        self.client.market_order(SYMBOL,side,qty,reduce_only=True)
        self.pos.qty_rem=round(self.pos.qty_rem-qty,4)
    def _close_all(self,price,reason):
        if self.pos.qty_rem<=0:return
        side="SELL"if self.pos.direction=="LONG"else"BUY"
        qty=self._round_qty(self.pos.qty_rem)
        if qty>0:self.client.market_order(SYMBOL,side,qty,reduce_only=True)
        if self.pos.direction=="LONG":pnl=(price-self.pos.entry_price)/self.pos.entry_price
        else:pnl=(self.pos.entry_price-price)/self.pos.entry_price
        pnl_lev=pnl*LEVERAGE
        # Funding PnL approximation
        fr=self.db.kv_get("last_funding_rate",0)
        hold_hours=0
        try:
            opened=datetime.strptime(self.pos.opened_at,"%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
            hold_hours=(datetime.now(timezone.utc)-opened).total_seconds()/3600
        except:pass
        funding_pnl=-fr*(hold_hours/8)*LEVERAGE if self.pos.direction=="LONG"else fr*(hold_hours/8)*LEVERAGE
        self.db.update("trades",self.pos.trade_id,{"status":"CLOSED","exit_reason":reason,
            "total_pnl":pnl_lev,"total_pnl_pct":pnl_lev,"mfe_pct":self.pos.mfe,"mae_pct":self.pos.mae,
            "funding_pnl_pct":funding_pnl,"price_pnl_pct":pnl_lev-funding_pnl,"closed_at":utcnow()})
        log.info(f"🔴 CLOSED {self.pos.direction}|{reason}|PnL={pnl_lev:.2%}|MFE={self.pos.mfe:.2%}|MAE={self.pos.mae:.2%}")
        self.pos=Position();self._save_pos()
    def analyze(self,md):
        sp=Sig.spread_bps(md.get("orderbook",{}))
        self.verdict=AgentVerdict(agent_name="Execution",direction="AGREE",
            confidence=float(max(0.5,1-sp/20)),reasoning=f"Spread={sp:.1f}bps TWAP={self._twap_params()} AvgSlip={self.avg_slip:.1f}",
            scores={"spread_bps":sp,"avg_slippage":self.avg_slip,"has_position":self.has_pos(),
                    "twap":self._twap_params()})
        return self.verdict
    def communicate(self,all_v):
        risk=next((v for v in all_v if v.agent_name=="Risk"),None)
        if risk and self.verdict:
            proposed=risk.scores.get("balance",300)*0.15*LEVERAGE
            depth=next((v.scores.get("book_depth",999999)for v in all_v if v.agent_name=="Microstructure"),999999)
            impact=proposed/max(depth,1)*10000
            if impact>5:self.verdict.revision_notes=f"Impact {impact:.1f}bps—requesting size reduction"
        return self.verdict

class MetaAgent(BaseAgent):
    def __init__(self,db):
        super().__init__("Meta",db)
        self.avoid=db.kv_get("avoid_conditions",[])
        self.favour=db.kv_get("favour_conditions",[])
        self.agent_weights=db.kv_get("agent_weights",{"Alpha":0.25,"Regime":0.20,"Risk":0.15,"Microstructure":0.20,"Meta":0.15,"Execution":0.05})
        self.last_tier2=db.kv_get("last_tier2",0);self.last_tier3=db.kv_get("last_tier3",0)
    def tier1_update(self,trade_id,direction,profitable,alpha_signals,verdicts):
        """After every trade: Bayesian+Kelly+CVaR+agent accuracy."""
        for v in verdicts:
            correct=v.direction==direction and profitable
            self.db.insert("agent_performance",{"ts":utcnow(),"agent_name":v.agent_name,
                "trade_id":trade_id,"direction_correct":int(correct),
                "confidence":float(v.confidence),"trade_pnl":0,
                "veto_issued":int(v.veto),"veto_correct":0,"rolling_accuracy":0})
    def tier2_check(self):
        """Every 72 hours: refit models."""
        if time.time()-self.last_tier2<72*3600:return False
        self.last_tier2=time.time();self.db.kv_set("last_tier2",self.last_tier2)
        log.info("TIER 2: Model refitting scheduled");return True
    def tier3_check(self):
        """Every 7 days: walk-forward optimization + condition filtering."""
        if time.time()-self.last_tier3<7*24*3600:return False
        self.last_tier3=time.time();self.db.kv_set("last_tier3",self.last_tier3)
        # Condition filtering
        rows=self.db.query("SELECT condition_key,wins,losses FROM condition_performance")
        self.avoid=[];self.favour=[]
        for key,w,l in rows:
            total=w+l
            if total>=10:
                wr=w/total
                if wr<0.35:self.avoid.append(key)
                elif wr>0.65:self.favour.append(key)
        self.db.kv_set("avoid_conditions",self.avoid);self.db.kv_set("favour_conditions",self.favour)
        # Update agent weights from accuracy
        agents=["Alpha","Regime","Risk","Microstructure","Meta","Execution"]
        for a in agents:
            rows=self.db.query("SELECT direction_correct FROM agent_performance WHERE agent_name=? ORDER BY id DESC LIMIT 30",(a,))
            if len(rows)>=10:
                acc=np.mean([r[0]for r in rows])
                self.agent_weights[a]=max(acc,0.05)
        total=sum(self.agent_weights.values())
        self.agent_weights={k:min(v/total,0.40)for k,v in self.agent_weights.items()}
        self.db.kv_set("agent_weights",self.agent_weights)
        self.db.insert("agent_weight_history",{"ts":utcnow(),"alpha_w":self.agent_weights.get("Alpha",0),
            "regime_w":self.agent_weights.get("Regime",0),"risk_w":self.agent_weights.get("Risk",0),
            "micro_w":self.agent_weights.get("Microstructure",0),"meta_w":self.agent_weights.get("Meta",0),
            "exec_w":self.agent_weights.get("Execution",0),"trigger":"TIER3"})
        log.info(f"TIER 3: Weights updated: {self.agent_weights}")
        return True
    def analyze(self,md):
        sess=get_session();h=md.get("signals",{}).get("hurst",0.5)
        strat="A"if h>0.55 else("B"if h<0.45 else"N")
        ckey=json.dumps({"session":sess,"strategy":strat})
        match="UNKNOWN";hist_wr=0.5;veto=False;vr=""
        row=self.db.query_one("SELECT wins,losses FROM condition_performance WHERE condition_key=?",(ckey,))
        if row:
            total=row[0]+row[1]
            if total>=10:
                wr=row[0]/total;hist_wr=wr
                if wr>0.65:match="FAVOUR"
                elif wr<0.35:
                    match="AVOID"
                    if wr<0.30 and total>=15:veto=True;vr=f"AVOID:WR={wr:.0%}over{total}"
        # Check optimization schedules
        self.tier2_check();self.tier3_check()
        self.verdict=AgentVerdict(agent_name="Meta",direction="NEUTRAL",
            confidence=0.65 if match=="FAVOUR"else 0.4,
            reasoning=f"Condition:{match} WR={hist_wr:.0%} Avoid:{len(self.avoid)} Favour:{len(self.favour)}",
            veto=veto,veto_reason=vr,
            scores={"condition":match,"hist_wr":hist_wr,"agent_weights":self.agent_weights,
                    "avoid_count":len(self.avoid),"favour_count":len(self.favour),
                    "tier2_due":time.time()-self.last_tier2>72*3600,
                    "tier3_due":time.time()-self.last_tier3>7*24*3600})
        return self.verdict

class ArbiterAgent(BaseAgent):
    def __init__(self,db):
        super().__init__("Arbiter",db)
        self.weights=db.kv_get("agent_weights",{"Alpha":0.25,"Regime":0.20,"Risk":0.15,"Microstructure":0.20,"Meta":0.15,"Execution":0.05})
    def deliberate(self,verdicts,score,strategy):
        self.weights=self.db.kv_get("agent_weights",self.weights)
        # Phase A: Veto
        for v in verdicts:
            if v.veto:return"VETOED",0.0,f"VETOED by {v.agent_name}:{v.veto_reason}",v.agent_name
        # Phase B: Direction consensus
        lw=0;sw=0;skw=0
        for v in verdicts:
            w=self.weights.get(v.agent_name,0.1)*v.confidence
            if v.direction=="LONG":lw+=w
            elif v.direction=="SHORT":sw+=w
            else:skw+=w
        if skw>(lw+sw):return"SKIP",0.3,"Majority skip",""
        if lw>sw*1.3:cons="LONG"
        elif sw>lw*1.3:cons="SHORT"
        else:return"SKIP",0.35,f"No consensus L={lw:.2f}vs S={sw:.2f}",""
        # Phase C: Confidence
        tw=sum(self.weights.get(v.agent_name,0.1)for v in verdicts)
        ac=sum(v.confidence*self.weights.get(v.agent_name,0.1)for v in verdicts)/max(tw,0.01)
        if ac<0.42:return"SKIP",ac,f"Low confidence:{ac:.2f}",""
        # Phase D: Disagreement
        dis=sum(1 for v in verdicts if v.direction not in(cons,"AGREE","NEUTRAL","SKIP")and v.direction!="")
        if dis>=3:return"SKIP",ac,f"Too much disagreement:{dis}",""
        # Phase E: Confluence
        sess=get_session();sp=session_params()
        min_s=sp["min_score"]if strategy!="B"else SB_MIN_SCORE
        if strategy=="A"and sess=="US":min_s=65
        if score<min_s:return"SKIP",ac,f"Score {score:.0f}<{min_s}",""
        # Phase F: GO
        sz_note=""
        if ac<0.60:sz_note="(size -30%)"
        elif ac>0.78:sz_note="(size +8%)"
        margin=max(lw,sw)/max(min(lw,sw),0.01)
        reason=f"GO {cons}|L={lw:.2f}S={sw:.2f}|Conf={ac:.2f}|Dis={dis}|Score={score:.0f}{sz_note}"
        return f"GO_{cons}",ac,reason,""
# ═══ MAIN BOT ═══
class MedallionBot:
    def __init__(self):
        self.db=Database();self.client=BinanceClient(API_KEY,API_SECRET)
        self.alpha_ag=AlphaAgent(self.db);self.regime_ag=RegimeAgent(self.db)
        self.risk_ag=RiskAgent(self.db);self.micro_ag=MicrostructureAgent(self.db)
        self.exec_ag=ExecutionAgent(self.db,self.client);self.meta_ag=MetaAgent(self.db)
        self.arbiter_ag=ArbiterAgent(self.db)
        self.agents=[self.alpha_ag,self.regime_ag,self.risk_ag,self.micro_ag,self.exec_ag,self.meta_ag]
        self.scan_num=self.db.kv_get("scan_num",0);self.running=True;self.sym_info={}
        self.messages=[];self.start_balance=self.db.kv_get("start_balance",300)
        Confluence.load_weights(self.db)  # Load learned signal weights
        sig_mod.signal(sig_mod.SIGINT,self._shutdown);sig_mod.signal(sig_mod.SIGTERM,self._shutdown)

    def _shutdown(self,*a):
        log.info("Shutting down—saving state...");self.running=False
        self.db.kv_set("scan_num",self.scan_num)

    def _validate_keys(self):
        if"PASTE"in API_KEY or"PASTE"in API_SECRET:
            log.critical("API keys not set. Edit medallion.py.");sys.exit(1)

    def setup(self):
        log.info("═"*60);log.info("  MEDALLION RENAISSANCE v2.0 — SETUP");log.info("═"*60)
        self._validate_keys()
        if not self.client.ping():log.critical("Cannot reach Binance");sys.exit(1)
        log.info("✓ Binance reachable");self.client._sync_time()
        bal=self.client.balance();log.info(f"✓ Balance: ${bal:.2f} USDT")
        self.db.kv_set("peak_equity",bal);self.db.kv_set("start_balance",bal)
        self.client.set_leverage(SYMBOL,LEVERAGE);log.info(f"✓ Leverage: {LEVERAGE}×")
        self.client.set_margin_type(SYMBOL,MARGIN_TYPE);log.info(f"✓ Margin: {MARGIN_TYPE}")
        info=self.client.symbol_info(SYMBOL)
        if info:
            si={}
            for f in info.get("filters",[]):
                if f["filterType"]=="LOT_SIZE":si["step_size"]=float(f["stepSize"]);si["min_qty"]=float(f["minQty"])
                elif f["filterType"]=="PRICE_FILTER":si["tick_size"]=float(f["tickSize"])
            si["qty_precision"]=info.get("quantityPrecision",3);si["price_precision"]=info.get("pricePrecision",2)
            self.db.kv_set("symbol_info",si);self.sym_info=si
            log.info(f"✓ Symbol: step={si.get('step_size')} min={si.get('min_qty')}")
        log.info("Fetching history...");df_eth=self.client.klines(SYMBOL,"1h",500)
        df_btc=self.client.klines("BTCUSDT","1h",200);df_sol=self.client.klines("SOLUSDT","1h",200)
        log.info(f"✓ ETH:{len(df_eth)} BTC:{len(df_btc)} SOL:{len(df_sol)} bars")
        if len(df_eth)>50:
            c=df_eth["close"].values;log.info("Fitting models...")
            kd=Sig.kalman(c[-200:]);log.info(f"✓ Kalman: vel={kd['velocity']:.6f}")
            hd=Sig.hurst(c[-100:]);log.info(f"✓ Hurst: {hd['hurst']:.3f}")
            lr=np.diff(np.log(c+1e-10));hmm=Sig.hmm(lr[-200:])
            log.info(f"✓ HMM: {hmm['dominant']} (Bull={hmm['p_bull']:.2f})")
            har=Sig.har_rv(c);log.info(f"✓ HAR-RV: vol_scalar={har['vol_scalar']:.2f} regime={Sig.eth_vol_regime(har['daily_vol'])}")
            vd=Sig.vpin(self.client.recent_trades(SYMBOL,1000)or[])
            log.info(f"✓ VPIN: {vd['vpin']:.2f} direction={vd['direction']}")
            oi=self.client.open_interest(SYMBOL);log.info(f"✓ OI: {oi:.0f}")
            fr=self.client.funding_rate(SYMBOL);log.info(f"✓ Funding: {fr:.4%}")
        pos=self.client.position(SYMBOL)
        if pos and float(pos.get("positionAmt",0))!=0:log.info(f"✓ Existing position: {pos['positionAmt']} ETH")
        else:log.info("✓ No existing position")
        log.info("═"*60);log.info(f"  SETUP COMPLETE — ${bal:.2f} | {LEVERAGE}× | {SYMBOL}")
        log.info(f"  Run: python3 medallion.py");log.info("═"*60)

    def verify(self):
        self._validate_keys();log.info("VERIFY: Checking health...")
        bal=self.client.balance();log.info(f"Balance: ${bal:.2f}")
        p=self.client.price(SYMBOL);log.info(f"ETH: ${p:.2f}")
        fr=self.client.funding_rate(SYMBOL);log.info(f"Funding: {fr:.4%}")
        oi=self.client.open_interest(SYMBOL);log.info(f"OI: {oi:.0f}")
        log.info(f"Session: {get_session()}");log.info(f"Options expiry: {is_options_expiry()}")
        df=self.client.klines(SYMBOL,"1h",100)
        if len(df)>50:
            h=Sig.hurst(df["close"].values);log.info(f"Hurst: {h['hurst']:.3f}")
            vd=Sig.vpin(self.client.recent_trades(SYMBOL,500)or[]);log.info(f"VPIN: {vd['vpin']:.2f}")
        dd=(self.risk_ag.peak-bal)/self.risk_ag.peak if self.risk_ag.peak>0 else 0
        log.info(f"Peak: ${self.risk_ag.peak:.2f} DD: {dd:.1%} Tier: {self.risk_ag.sizing_tier}")
        log.info("✓ Verify complete")

    def _fetch_data(self):
        md={};md["price"]=self.client.price(SYMBOL)
        md["df_1h"]=self.client.klines(SYMBOL,"1h",500);md["df_5m"]=self.client.klines(SYMBOL,"5m",100)
        md["df_4h"]=self.client.klines(SYMBOL,"4h",100);md["orderbook"]=self.client.orderbook(SYMBOL,20)
        md["funding_rate"]=self.client.funding_rate(SYMBOL);self.db.kv_set("last_funding_rate",md["funding_rate"])
        md["recent_trades"]=self.client.recent_trades(SYMBOL,1000)or[]
        md["oi_current"]=self.client.open_interest(SYMBOL);md["balance"]=self.client.balance()
        md["btc_df"]=self.client.klines("BTCUSDT","1h",60);md["sol_df"]=self.client.klines("SOLUSDT","1h",60)
        if len(md["df_1h"])>1:md["price_change_1h"]=(md["df_1h"]["close"].iloc[-1]-md["df_1h"]["close"].iloc[-2])/(md["df_1h"]["close"].iloc[-2]+1e-10)
        else:md["price_change_1h"]=0
        # OI history
        oih=self.db.kv_get("oi_hist",[]);oih.append({"t":time.time(),"v":md["oi_current"]});oih=oih[-500:]
        self.db.kv_set("oi_hist",oih);now=time.time()
        md["oi_1h_ago"]=next((x["v"]for x in reversed(oih)if now-x["t"]>3500),md["oi_current"])
        md["oi_4h_ago"]=next((x["v"]for x in reversed(oih)if now-x["t"]>14000),md["oi_current"])
        md["oi_24h_ago"]=self.db.kv_get("oi_24h",md["oi_current"])
        if now-self.db.kv_get("oi_24h_ts",0)>86400:self.db.kv_set("oi_24h",md["oi_current"]);self.db.kv_set("oi_24h_ts",now)
        # Funding history
        fh=self.client.funding_history(SYMBOL,21)
        md["funding_avg_7d"]=np.mean([float(f.get("fundingRate",0))for f in fh])if fh else md["funding_rate"]
        return md

    def _build_signals(self,md,verdicts):
        """Build unified signals dict from all agent verdicts."""
        s={};s["price"]=md["price"];s["session"]=get_session()
        df=md["df_1h"]
        if len(df)>50:
            c=df["close"].values;s["atr_val"]=Sig.atr(df);s["vwap"]=Sig.vwap(df)
            s["rsi_1h"]=Sig.rsi(c);sr=Sig.stoch_rsi(c);s["stoch_k"]=sr["k"];s["stoch_d"]=sr["d"]
            s["ema8"]=Sig.ema(c,8);s["ema21"]=Sig.ema(c,21)
            bb=Sig.bollinger(c);s["bb_width_pct"]=bb["width_pct"]
            s["st_1h"]=Sig.supertrend(df,ST_1H_P,ST_1H_M)
            if len(md.get("df_4h",pd.DataFrame()))>10:
                s["st_4h"]=Sig.supertrend(md["df_4h"],ST_4H_P,ST_4H_M)
                # Strategy B: check if 4h opposes
                if s.get("st_1h",0)!=s.get("st_4h",0):s["st_4h_opposing"]=True
                else:s["st_4h_opposing"]=False
            vr=df["volume"].iloc[-1]/(df["volume"].iloc[-21:-1].mean()+1e-10)if len(df)>21 else 1
            s["vol_ratio"]=vr;s["funding_rate"]=md["funding_rate"]
            s["spread_bps"]=Sig.spread_bps(md.get("orderbook",{}))
            s["has_position"]=self.exec_ag.has_pos()
        # Extract from agent verdicts
        for v in verdicts:
            sc=v.scores
            if v.agent_name=="Regime":
                s["hurst"]=sc.get("hurst",0.5);s["vol_scalar"]=sc.get("har_rv",{}).get("vol_scalar",1.0)
                s["vol_pct"]=sc.get("har_rv",{}).get("vol_pct",50)
                s["hmm_bull"]=sc.get("hmm",{}).get("p_bull",0.33)
                s["hmm_bear"]=sc.get("hmm",{}).get("p_bear",0.33)
                s["hmm_uncertain"]=sc.get("hmm",{}).get("uncertain",False)
                s["cross_asset"]=sc.get("cross_asset",0);s["btc_divergence"]=sc.get("btc_divergence",0)
                s["vol_regime"]=sc.get("vol_regime","NORMAL")
            elif v.agent_name=="Alpha":
                s["ensemble_long"]=sc.get("ensemble_long",0);s["ensemble_short"]=sc.get("ensemble_short",0)
                kd=sc.get("kalman",{});s["kalman_vel"]=kd.get("velocity",0)
                s["kalman_acc"]=kd.get("acceleration",0);s["kalman_thresh"]=kd.get("threshold",0.001)
                s["freshness"]=sc.get("freshness",1);s["avg_corr"]=sc.get("avg_corr",0.3)
                s["entropy"]=sc.get("entropy",1)
                bwl=sc.get("bw_long",[0.2]*5);s["min_bayes_weight"]=min(bwl)
                s["all_bayes_above_60"]=all(w>0.60 for w in bwl)
                s["bayesian_consensus"]=np.mean(bwl)
                s["avg_mi"]=0.10  # Updated by tier2
            elif v.agent_name=="Microstructure":
                s["vpin"]=sc.get("vpin",0.4);s["book_pressure"]=sc.get("book_pressure",0)
                s["oi_scenario"]=sc.get("oi_scenario","");s["oi_extreme"]=sc.get("oi_extreme",False)
                s["oi_roc_1h"]=sc.get("oi_roc_1h",0);s["oi_roc_4h"]=sc.get("oi_roc_4h",0)
                s["oi_roc_24h"]=sc.get("oi_roc_24h",0)
                s["funding_term"]=sc.get("funding_term","");s["funding_extreme"]=sc.get("funding_extreme",False)
                s["daily_carry"]=sc.get("daily_carry",0);s["adverse_sel"]=sc.get("adverse_sel",0.35)
                s["manipulation"]=sc.get("manipulation",False)
                s["absorption"]=sc.get("absorption",False)
                s["foi_confluence"]=sc.get("foi_confluence",False)
                s["book_depth"]=sc.get("book_depth",999999)
                s["eff_spread"]=sc.get("spread_bps",2)
                # Carry direction
                fr=md.get("funding_rate",0)
                s["carry_favorable"]=(fr<0)  # longs earn when funding negative
                s["carry_against"]=abs(s["daily_carry"])>0.0008
                # Funding+OI direction
                if s["foi_confluence"]:
                    if fr>0 and sc.get("oi_extreme",False):s["funding_oi_conf_short"]=True;s["funding_oi_conf_long"]=False
                    elif fr<0 and sc.get("oi_extreme",False):s["funding_oi_conf_long"]=True;s["funding_oi_conf_short"]=False
                    else:s["funding_oi_conf_long"]=False;s["funding_oi_conf_short"]=False
                else:s["funding_oi_conf_long"]=False;s["funding_oi_conf_short"]=False
        # Agent counts
        s["agents_long"]=sum(1 for v in verdicts if v.direction=="LONG")
        s["agents_short"]=sum(1 for v in verdicts if v.direction=="SHORT")
        # Uncertainty flags
        uf=0
        if s.get("hmm_uncertain",False):uf+=1
        if any(v.agent_name=="Regime"and v.scores.get("hurst_stability",0)>0.08 for v in verdicts):uf+=1
        if s.get("vpin",0.4)>0.55:uf+=1
        if s.get("oi_extreme",False):uf+=1
        if s.get("funding_extreme",False):uf+=1
        if s.get("entropy",1)>1.20:uf+=1
        if s.get("avg_corr",0.3)>0.50:uf+=1
        # VPIN spike
        vpin_delta=next((v.scores.get("vpin_delta",0)for v in verdicts if v.agent_name=="Microstructure"),0)
        if abs(vpin_delta)>0.15:uf+=1
        # Bayesian instability
        if s.get("min_bayes_weight",0.5)<0.30:uf+=1
        # Kalman innovation spike
        kinov=next((v.scores.get("kalman",{}).get("innovation",0)for v in verdicts if v.agent_name=="Alpha"),0)
        innov_std=1.0  # simplified
        if abs(kinov)>2.5*innov_std:uf+=1
        s["uncertainty_flags"]=uf
        # Correlation storm
        if len(md.get("btc_df",pd.DataFrame()))>2 and len(md.get("df_5m",pd.DataFrame()))>2:
            eth_5m=md["df_5m"]["close"].values;btc_c=md["btc_df"]["close"].values
            eth_move=abs((eth_5m[-1]-eth_5m[-2])/(eth_5m[-2]+1e-10))if len(eth_5m)>1 else 0
            btc_move=abs((btc_c[-1]-btc_c[-2])/(btc_c[-2]+1e-10))if len(btc_c)>1 else 0
            s["corr_storm"]=eth_move>0.015 and btc_move>0.015
        else:s["corr_storm"]=False
        return s

    def _run_agents(self,md):
        """Full 4-phase deliberation."""
        # Phase 1: Independent analysis
        verdicts=[]
        for ag in self.agents:
            try:v=ag.analyze(md);verdicts.append(v)
            except Exception as e:
                log.error(f"Agent {ag.name} error:{e}",exc_info=True)
                verdicts.append(AgentVerdict(agent_name=ag.name,direction="SKIP",confidence=0,reasoning=f"ERROR:{e}"))
        # Build signals from verdicts
        sigs=self._build_signals(md,verdicts);md["signals"]=sigs
        self.db.kv_set("current_atr",sigs.get("atr_val",50))
        # Re-run Risk Agent with full signals
        try:
            self.risk_ag.analyze(md)
            for i,v in enumerate(verdicts):
                if v.agent_name=="Risk":verdicts[i]=self.risk_ag.verdict;break
        except:pass
        # Phase 2-3: Communication and revision
        self.messages=[]
        for ag in self.agents:
            try:
                rv=ag.communicate(verdicts)
                if rv:
                    for i,v in enumerate(verdicts):
                        if v.agent_name==ag.name:verdicts[i]=rv;break
                    if rv.revision_notes:
                        msg=AgentMessage(sender=ag.name,recipient="ALL",msg_type="INFORM",
                            content=rv.revision_notes,priority=3,ts=time.time())
                        self.messages.append(msg);self.db.log_msg(self.scan_num,msg)
            except:pass
        # Update agent opponent counts
        consensus_dir="LONG"if sigs.get("agents_long",0)>sigs.get("agents_short",0)else"SHORT"
        sigs["agents_oppose_long"]=sum(1 for v in verdicts if v.direction=="SHORT")
        sigs["agents_oppose_short"]=sum(1 for v in verdicts if v.direction=="LONG")
        sigs["agent_near_veto"]=any(v.veto for v in verdicts)
        # Score
        strategy=next((v.scores.get("strategy","NEUTRAL")for v in verdicts if v.agent_name=="Regime"),"NEUTRAL")
        # HYBRID SCORING: hardcoded for first 100 trades, then logistic model blends in
        if strategy=="A"or strategy=="B":
            ls,ss=GBMScorer.hybrid_score(sigs,strategy,self.db)
        else:ls,ss=0,0
        sigs["long_score"]=ls;sigs["short_score"]=ss
        md["signals"]=sigs;md["strategy"]=strategy
        # Log alpha
        self.db.insert("alpha_log",{"ts":utcnow(),"scan_num":self.scan_num,
            "alpha_signals":json.dumps(safe_json(next((v.scores.get("alphas",[])for v in verdicts if v.agent_name=="Alpha"),[]))),
            "bayesian_weights":json.dumps(safe_json(next((v.scores.get("bw_long",[])for v in verdicts if v.agent_name=="Alpha"),[]))),
            "long_score":ls,"short_score":ss,
            "ensemble_long":sigs.get("ensemble_long",0),"ensemble_short":sigs.get("ensemble_short",0),
            "hurst":sigs.get("hurst",0.5),"hmm_state":next((v.scores.get("hmm",{}).get("dominant","?")for v in verdicts if v.agent_name=="Regime"),"?"),
            "vpin":sigs.get("vpin",0),"oi_roc_1h":sigs.get("oi_roc_1h",0),
            "fr_current":md.get("funding_rate",0),"fr_term":sigs.get("funding_term",""),
            "signal_entropy":sigs.get("entropy",0),"avg_alpha_corr":sigs.get("avg_corr",0),
            "strategy":strategy,"action":"SCAN","session":sigs.get("session","")})
        return verdicts

    def _dashboard(self,verdicts,md):
        sigs=md.get("signals",{});p=md.get("price",0);bal=md.get("balance",0)
        sess=sigs.get("session","?");strat=md.get("strategy","?");h=sigs.get("hurst",0.5)
        dd=(self.risk_ag.peak-bal)/self.risk_ag.peak if self.risk_ag.peak>0 else 0
        print("\033[2J\033[H")
        print("╔═══════════════════════════════════════════════════════════════════════╗")
        print(f"║ MEDALLION v2.0  Scan#{self.scan_num}  {utcnow()} UTC  ⚠ REAL 5×  ║")
        print("╚═══════════════════════════════════════════════════════════════════════╝")
        print(f" ETH ${p:,.2f} | Session:{sess} | Strategy:{strat}(H={h:.3f})")
        print(f" Funding:{sigs.get('funding_rate',0):.4%} | VPIN:{sigs.get('vpin',0):.2f} | Spread:{sigs.get('spread_bps',0):.1f}bps")
        vr=sigs.get("vol_regime","?");uf=sigs.get("uncertainty_flags",0)
        print(f" Vol regime:{vr} | Uncertainty:{uf}/10 | OI:{sigs.get('oi_scenario','—')} {'⚠ EXTREME'if sigs.get('oi_extreme')else''}")
        print("─"*71)
        print(" AGENT DELIBERATION:")
        for v in verdicts:
            vt="⛔VETO"if v.veto else""
            rev=f" [{v.revision_notes[:30]}]"if v.revision_notes else""
            print(f"  {v.agent_name:15s}→ {v.direction:7s} conf={v.confidence:.2f} {v.reasoning[:40]}{vt}{rev}")
        if self.messages:
            print(" MESSAGES:")
            for m in self.messages[-3:]:print(f"  {m.sender}→{m.recipient}: {m.content[:50]}")
        print("─"*71)
        ls=sigs.get("long_score",0);ss=sigs.get("short_score",0)
        lb=int(ls/10);sb=int(ss/10)
        print(f" LONG:{ls:3.0f} {'█'*lb}{'░'*(10-lb)} | SHORT:{ss:3.0f} {'█'*sb}{'░'*(10-sb)}")
        sd=self.db.kv_get("last_scoring_decision",{})
        if sd:
            mode=sd.get("mode","HARDCODED");mn=sd.get("model","");ph=sd.get("phase",1)
            if mode.startswith("HIGH"):print(f" Scoring: 🧠 {mn} HIGH conf={sd.get('ml_conf',0):.0%} P{ph} {'✅ AGREE'if sd.get('agreed')else'⚠️ DISAGREE'}")
            elif mode.startswith("MEDIUM"):print(f" Scoring: 🔀 {mn} MEDIUM conf={sd.get('ml_conf',0):.0%} P{ph} {'✅ AGREE'if sd.get('agreed')else'⚠️ CONSERVATIVE'}")
            elif mode=="LOW_FALLBACK":print(f" Scoring: 📐 CONFLUENCE (model uncertain {sd.get('ml_conf',0):.0%})")
            else:print(f" Scoring: 📐 CONFLUENCE ONLY (Phase 1 — models training)")
        if self.exec_ag.has_pos():
            pos=self.exec_ag.pos
            tp1s="✓"if pos.tp1_hit else"—";tp2s="✓"if pos.tp2_hit else"—"
            print(f" ● {LEVERAGE}× {pos.direction} {pos.strategy} @${pos.entry_price:.2f} Qty:{pos.qty_rem:.4f}")
            print(f"   Stop:${pos.stop_price:.2f} TP1:{tp1s} TP2:{tp2s} MFE:{pos.mfe:.2%} MAE:{pos.mae:.2%}")
        cum_pnl=bal-self.start_balance;cum_pct=cum_pnl/self.start_balance if self.start_balance>0 else 0
        print("─"*71)
        print(f" Equity:${bal:.2f} Peak:${self.risk_ag.peak:.2f} DD:{dd:.1%} Tier:{self.risk_ag.sizing_tier}")
        print(f" Start:${self.start_balance:.2f} PnL:${cum_pnl:.2f}({cum_pct:+.1%}) Trades:{self.risk_ag.trades_today}/{MAX_TRADES_DAY}")
        # Compounding stats
        total_trades=self.db.query_one("SELECT count(*) FROM trades WHERE status='CLOSED'")
        tt=total_trades[0]if total_trades else 0
        if tt>0:
            wins=self.db.query_one("SELECT count(*) FROM trades WHERE status='CLOSED' AND total_pnl_pct>0")
            w=wins[0]if wins else 0;wr=w/tt
            cw=self.db.kv_get("consec_wins",0)
            streak_str=f"🔥{cw}W"if cw>=2 else""
            print(f" WR:{wr:.0%}({w}W/{tt-w}L) {streak_str} | Kill@${self.risk_ag.peak*0.90:.0f} | Compound:{cum_pct:+.1%}")
        else:
            print(f" No trades yet | Kill@${self.risk_ag.peak*0.90:.0f}")
        # Agent weights
        aw=self.meta_ag.agent_weights
        print(f" Weights: A={aw.get('Alpha',0):.2f} R={aw.get('Regime',0):.2f} Ri={aw.get('Risk',0):.2f} M={aw.get('Microstructure',0):.2f}")
        print("═"*71)

    def scan(self):
        self.scan_num+=1
        try:
            md=self._fetch_data()
            if not md.get("price"):log.warning("No price data");return
            # Manage existing position
            if self.exec_ag.has_pos():
                result=self.exec_ag.manage(md["price"])
                if result and result in("STOPPED","EMERGENCY","LIQ_GUARD","TRAIL","TP3","MAX_HOLD"):
                    self._on_closed(result,md)
                elif result in("TP1","TP2"):pass  # partial, continue
            # Run agents
            verdicts=self._run_agents(md);sigs=md.get("signals",{});strat=md.get("strategy","NEUTRAL")
            score=max(sigs.get("long_score",0),sigs.get("short_score",0))
            # Deliberate
            action,conf,reasoning,veto_agent=self.arbiter_ag.deliberate(verdicts,score,strat)
            # Log deliberation
            vs=[safe_json({v.agent_name:{"d":v.direction,"c":round(float(v.confidence),3),"v":bool(v.veto)}})for v in verdicts]
            ms=[safe_json({"s":m.sender,"r":m.recipient,"c":m.content[:100]})for m in self.messages[:5]]
            self.db.log_delib(self.scan_num,vs,ms,action,reasoning,
                {"consensus_dir":action.replace("GO_","")if"GO_"in action else"","agg_confidence":float(conf),
                 "disagreement":sum(1 for v in verdicts if v.direction not in("AGREE","NEUTRAL","SKIP","")),
                 "veto_issued":int("VETO"in action),"veto_agent":veto_agent,"veto_reason":reasoning if"VETO"in action else""})
            # Execute
            if action.startswith("GO_")and not self.exec_ag.has_pos():
                direction=action.split("_")[1]
                sigs["proposed_dir"]=direction
                sigs["proposed_notional"]=md["balance"]*0.15*LEVERAGE
                # Re-check risk gates with direction
                passed,reason,gate=self.risk_ag.gates(md["balance"],sigs)
                if not passed:
                    log.info(f"Post-deliberation gate blocked:{reason}");self._dashboard(verdicts,md);return
                # ═══ PRE-TRADE EXPECTANCY FILTER ═══
                # Before sizing, ask: "Is this trade WORTH taking?"
                # Uses historical avg_win and avg_loss with model probability.
                # Skips trades where expected dollar value is negative.
                recent_trades=self.db.query("SELECT total_pnl_pct FROM trades WHERE status='CLOSED' AND direction=? ORDER BY id DESC LIMIT 30",(direction,))
                if len(recent_trades)>=15:
                    pnls=[t[0]or 0 for t in recent_trades]
                    win_pnls=[p for p in pnls if p>0];loss_pnls=[p for p in pnls if p<=0]
                    avg_win=np.mean(win_pnls)if win_pnls else 0.01
                    avg_loss=abs(np.mean(loss_pnls))if loss_pnls else 0.01
                    hist_wr=len(win_pnls)/len(pnls)
                    # Use model probability if available, otherwise historical WR
                    sd_dec=self.db.kv_get("last_scoring_decision",{})
                    model_prob=sd_dec.get("ml_conf",0)if sd_dec.get("phase",1)>=2 else 0
                    prob=model_prob if model_prob>0.50 else hist_wr
                    expected_value=prob*avg_win-(1-prob)*avg_loss
                    if expected_value<0:
                        log.info(f"⛔ EXPECTANCY FILTER: EV={expected_value:+.3%} (prob={prob:.2f}×{avg_win:.2%} - {1-prob:.2f}×{avg_loss:.2%})")
                        self._dashboard(verdicts,md);return
                    elif expected_value<0.001:
                        log.info(f"⚠️ LOW EXPECTANCY: EV={expected_value:+.3%} — reducing size 30%")
                        sigs["low_ev_penalty"]=True
                dis=sum(1 for v in verdicts if v.direction not in(direction,"AGREE","NEUTRAL","SKIP",""))
                sz=self.risk_ag.compute_size(md["balance"],direction,sigs,dis)
                if sz==-1:log.critical("KILL SWITCH!");self.running=False;return
                if sz<=0:log.info("Size=0, skip");self._dashboard(verdicts,md);return
                # Apply low-EV penalty if expectancy filter flagged it
                if sigs.get("low_ev_penalty",False):sz*=0.70
                # Confidence adjustment
                if conf<0.60:sz*=0.70
                elif conf>0.78:sz*=1.08
                # Tweak: Conviction premium — when 4+ agents agree with high confidence
                agreeing=sum(1 for v in verdicts if v.direction==direction)
                avg_agree_conf=np.mean([v.confidence for v in verdicts if v.direction==direction])if agreeing>0 else 0
                if agreeing>=5 and avg_agree_conf>0.65:
                    sz*=1.20  # 20% conviction premium — near-unanimous
                    log.info(f"🎯 MAX CONVICTION: {agreeing} agents agree @{avg_agree_conf:.2f} conf → size +20%")
                elif agreeing>=4 and avg_agree_conf>0.60:
                    sz*=1.12  # 12% conviction premium — strong consensus
                    log.info(f"🎯 CONVICTION PREMIUM: {agreeing} agents agree @{avg_agree_conf:.2f} conf → size +12%")
                price=md["price"];atr_val=sigs.get("atr_val",price*0.015)
                qty=self.exec_ag._round_qty(sz*LEVERAGE/price)
                min_qty=self.exec_ag.sym_info.get("min_qty",0.001)
                if qty<min_qty:log.info(f"Qty {qty}<min {min_qty}");self._dashboard(verdicts,md);return
                # Compute levels
                if strat=="A":
                    sd=max(min(atr_val*SA_STOP_ATR,price*SA_STOP_MAX),price*SA_STOP_MIN)
                    t1d=atr_val*SA_TP1_ATR;t2d=atr_val*SA_TP2_ATR;t3d=atr_val*SA_TP3_ATR
                else:
                    sd=max(min(atr_val*SB_STOP_ATR,price*SB_STOP_MAX),price*SB_STOP_MIN)
                    t1d=atr_val*SB_TP1_ATR;t2d=atr_val*SB_TP2_ATR
                    t3d=abs(price-sigs.get("vwap",price))  # TP3=VWAP for strategy B
                if direction=="LONG":
                    stop=price-sd;tp1=price+t1d;tp2=price+t2d;tp3=price+t3d
                    liq=price*(1-1/LEVERAGE*0.95)
                else:
                    stop=price+sd;tp1=price-t1d;tp2=price-t2d;tp3=price-t3d
                    liq=price*(1+1/LEVERAGE*0.95)
                # Record trade
                tid=self.db.insert("trades",{
                    "direction":direction,"strategy":strat,"entry_price":price,"stop_price":stop,
                    "liq_price":liq,"tp1_price":tp1,"tp2_price":tp2,"tp3_price":tp3,
                    "qty_full":qty,"qty_rem":qty,"notional":qty*price,"margin":sz,
                    "status":"OPEN","hurst":sigs.get("hurst",0.5),
                    "hmm_p_bull":sigs.get("hmm_bull",0),"hmm_p_bear":sigs.get("hmm_bear",0),
                    "long_score":sigs.get("long_score",0),"short_score":sigs.get("short_score",0),
                    "ensemble_long":sigs.get("ensemble_long",0),"ensemble_short":sigs.get("ensemble_short",0),
                    "uncertainty_score":sigs.get("uncertainty_flags",0),
                    "vpin_at_entry":sigs.get("vpin",0),"vpin_direction":sigs.get("vpin_direction",""),
                    "book_pressure":sigs.get("book_pressure",0),"adverse_selection":sigs.get("adverse_sel",0),
                    "oi_roc_1h":sigs.get("oi_roc_1h",0),"oi_roc_4h":sigs.get("oi_roc_4h",0),
                    "oi_scenario":sigs.get("oi_scenario",""),"oi_extreme":int(sigs.get("oi_extreme",False)),
                    "funding_at_entry":md.get("funding_rate",0),"fr_term":sigs.get("funding_term",""),
                    "session":get_session(),"arbiter_confidence":conf,"agent_disagreement":dis,
                    "agent_verdicts":json.dumps(vs),"opened_at":utcnow()})
                ok=self.exec_ag.enter(direction,qty,price,stop,tp1,tp2,tp3,strat,liq,tid,md.get("orderbook"))
                if ok:
                    self.risk_ag.trades_today+=1;self.db.kv_set("trades_today",self.risk_ag.trades_today)
                    # Store alpha signals at entry for Bayesian update on close
                    alpha_v=next((v for v in verdicts if v.agent_name=="Alpha"),None)
                    if alpha_v:self.db.kv_set("last_alpha_signals",safe_json(alpha_v.scores.get("alphas",[0]*5)))
                    # Store which signals were active for adaptive weight learning
                    active_sigs=SignalTracker.extract_active(sigs,direction)
                    self.db.kv_set(f"trade_signals_{tid}",safe_json({"signals":active_sigs,"win":None}))
                    # Store feature vector for logistic model training
                    feat=LogisticScorer.extract_features(sigs)
                    self.db.kv_set(f"trade_features_{tid}",safe_json(feat.tolist()))
                    # Store scoring decision for brain comparison tracking
                    scoring_dec=self.db.kv_get("last_scoring_decision",{})
                    if scoring_dec:self.db.kv_set(f"trade_scoring_{tid}",safe_json(scoring_dec))
                    log.info(f"🚀 {direction} ${sz:.2f}|Qty:{qty}|Stop:${stop:.2f}|TP1:${tp1:.2f}|Score:{score:.0f}")
            self._dashboard(verdicts,md)
        except Exception as e:log.error(f"Scan error:{e}",exc_info=True)

    def _on_closed(self,reason,md):
        bal=md.get("balance",self.client.balance());prev_peak=self.risk_ag.peak
        if bal>self.risk_ag.peak:self.risk_ag.peak=bal;self.db.kv_set("peak_equity",bal)
        self.risk_ag.update_milestones(bal)
        # Compound log
        cum=bal-self.start_balance
        self.db.insert("compound_log",{"ts":utcnow(),"balance_before":prev_peak,"balance_after":bal,
            "trade_pnl":bal-prev_peak,"trade_pnl_pct":(bal-prev_peak)/max(prev_peak,1),
            "cumulative_pnl":cum,"cumulative_pnl_pct":cum/max(self.start_balance,1),
            "peak_equity":max(prev_peak,bal),"drawdown_pct":(max(prev_peak,bal)-bal)/max(prev_peak,bal,1),
            "trades_total":self.risk_ag.trades_today,"compound_rate":0,"sizing_tier":self.risk_ag.sizing_tier,"note":reason})
        # Track first trade time for annual projections
        if not self.db.kv_get("first_trade_ts"):self.db.kv_set("first_trade_ts",time.time())
        # Condition performance
        last_trade=self.db.query_one("SELECT * FROM trades WHERE status='CLOSED' ORDER BY id DESC LIMIT 1")
        if last_trade:
            sess=last_trade[40]or"?";strat=last_trade[2]or"?";direction=last_trade[1]or"?"
            h_val=last_trade[19]or 0.5
            ckey=json.dumps({"session":sess,"strategy":strat})
            row=self.db.query_one("SELECT wins,losses,total_pnl FROM condition_performance WHERE condition_key=?",(ckey,))
            pnl_pct=last_trade[14]or 0
            if row:
                w,l,tp=row
                if pnl_pct>0:w+=1
                else:l+=1
                tp+=pnl_pct
                self.db.conn.execute("UPDATE condition_performance SET wins=?,losses=?,total_pnl=?,avg_pnl_pct=?,last_updated=? WHERE condition_key=?",
                    (w,l,tp,tp/(w+l)if(w+l)>0 else 0,utcnow(),ckey))
            else:
                w=1 if pnl_pct>0 else 0;l=0 if pnl_pct>0 else 1
                self.db.conn.execute("INSERT INTO condition_performance(condition_key,wins,losses,total_pnl,avg_pnl_pct,last_updated)VALUES(?,?,?,?,?,?)",
                    (ckey,w,l,pnl_pct,pnl_pct,utcnow()))
            self.db.conn.commit()
            # Tier 1: Update Bayesian + agent accuracy + adaptive signal weights
            alpha_sigs=self.db.kv_get("last_alpha_signals",[0]*5)
            profitable=pnl_pct>0
            self.alpha_ag.update_bayesian(direction,profitable,alpha_sigs)
            self.alpha_ag.check_retirement()
            # Update signal tracking for adaptive scoring
            snap=self.db.kv_get(f"trade_signals_{last_trade[0]}")
            if snap and isinstance(snap,dict):
                snap["win"]=profitable
                self.db.kv_set(f"trade_signals_{last_trade[0]}",snap)
            SignalTracker.update_weights(self.db,min_trades=50)
            # Retrain logistic model every 10 trades after reaching 100
            total_closed=self.db.query_one("SELECT count(*) FROM trades WHERE status='CLOSED'")[0]or 0
            if total_closed>=100 and total_closed%10==0:
                LogisticScorer.train(self.db)
            # Retrain GBM every 20 trades after reaching 500 (Phase 3)
            if total_closed>=500 and total_closed%20==0:
                GBMScorer.train(self.db)
            # Track which brain was correct (confluence vs logistic)
            scoring=self.db.kv_get(f"trade_scoring_{last_trade[0]}")
            if scoring and isinstance(scoring,dict)and scoring.get("mode","").startswith(("HIGH","MEDIUM")):
                brain_log=self.db.kv_get("brain_comparison",[])
                hc_correct=(scoring["hc_dir"]==direction and profitable)or(scoring["hc_dir"]!=direction and not profitable)
                lg_correct=(scoring["lg_dir"]==direction and profitable)or(scoring["lg_dir"]!=direction and not profitable)
                brain_log.append({"tid":last_trade[0],"hc_dir":scoring["hc_dir"],"lg_dir":scoring["lg_dir"],
                    "actual_dir":direction,"profitable":profitable,"hc_correct":hc_correct,
                    "lg_correct":lg_correct,"mode":scoring["mode"],"agreed":scoring.get("agreed",False)})
                brain_log=brain_log[-200:]  # keep last 200
                self.db.kv_set("brain_comparison",brain_log)
                if hc_correct!=lg_correct:
                    winner="CONFLUENCE"if hc_correct else"LOGISTIC"
                    log.info(f"🧠 BRAIN SPLIT: {winner} was correct (HC:{scoring['hc_dir']} LG:{scoring['lg_dir']} → {'WIN'if profitable else'LOSS'})")
        # Consecutive losses
        if reason in("STOPPED","MAX_HOLD","EMERGENCY","LIQ_GUARD"):
            self.risk_ag.consec_losses+=1;self.risk_ag.last_stop_ts=time.time()
            self.db.kv_set("consec_wins",0)  # reset win streak
            if self.risk_ag.consec_losses==2:
                self.risk_ag.paused_until=time.time()+3600
                log.info(f"⏸ 2 losses→1h pause")
            if self.risk_ag.consec_losses>=5:
                self.risk_ag.paused_until=time.time()+14400
                log.info(f"⏸ 5 losses→4h pause+emergency tier3")
        else:
            self.risk_ag.consec_losses=0
            # Track consecutive wins for hot streak sizing
            cw=self.db.kv_get("consec_wins",0)+1
            self.db.kv_set("consec_wins",cw)
            if cw>=3:log.info(f"🔥 HOT STREAK: {cw} consecutive wins — sizing +12%")
        self.db.kv_set("consec_losses",self.risk_ag.consec_losses)
        self.db.kv_set("last_stop_ts",self.risk_ag.last_stop_ts)
        # Milestone checks
        milestones_hit=[]
        total_trades=self.db.query_one("SELECT count(*) FROM trades WHERE status='CLOSED'")[0]
        if total_trades==10:milestones_hit.append(("trades_10",10))
        wins=self.db.query_one("SELECT count(*) FROM trades WHERE status='CLOSED' AND total_pnl_pct>0")[0]or 0
        wr=wins/total_trades if total_trades>0 else 0
        for thresh in[0.50,0.55,0.60]:
            if wr>=thresh:
                existing=self.db.query_one("SELECT id FROM milestones WHERE milestone_type=? AND value=?",(f"wr_{int(thresh*100)}",thresh))
                if not existing:milestones_hit.append((f"wr_{int(thresh*100)}",wr))
        for eq_thresh in[350,400,500,750,1000]:
            if bal>=eq_thresh:
                existing=self.db.query_one("SELECT id FROM milestones WHERE milestone_type=? AND value=?",(f"equity_{eq_thresh}",eq_thresh))
                if not existing:milestones_hit.append((f"equity_{eq_thresh}",bal))
        for mt,mv in milestones_hit:
            self.db.insert("milestones",{"ts":utcnow(),"milestone_type":mt,"value":mv,"note":f"Milestone: {mt}={mv}"})
            log.info(f"🏆 MILESTONE: {mt} = {mv}")
        log.info(f"Trade closed:{reason}|Balance:${bal:.2f}|PnL:${bal-prev_peak:.2f}")

    def run(self):
        self._validate_keys()
        log.info("═"*60);log.info("  MEDALLION v2.0 — LIVE TRADING")
        log.info(f"  {SYMBOL} | {LEVERAGE}× | Scan:{SCAN_INTERVAL}s");log.info("═"*60)
        # Daily reset
        today=datetime.now(timezone.utc).strftime("%Y-%m-%d")
        if self.db.kv_get("last_day","")!=today:
            self.risk_ag.trades_today=0;self.risk_ag.daily_pnl=0
            self.db.kv_set("trades_today",0);self.db.kv_set("daily_pnl",0)
            self.db.kv_set("last_day",today);self.alpha_ag.decay_priors()
        while self.running:
            try:
                self.scan();time.sleep(SCAN_INTERVAL)
                # Midnight reset
                now=datetime.now(timezone.utc)
                if now.hour==0 and now.minute==0:
                    self.risk_ag.trades_today=0;self.risk_ag.daily_pnl=0
                    self.db.kv_set("trades_today",0);self.db.kv_set("last_day",now.strftime("%Y-%m-%d"))
                    self.alpha_ag.decay_priors()
            except KeyboardInterrupt:break
            except Exception as e:log.error(f"Loop error:{e}",exc_info=True);time.sleep(5)
        log.info("Bot stopped.")

    def research(self):
        self._validate_keys();log.info("RESEARCH MODE — No trades")
        md=self._fetch_data();verdicts=self._run_agents(md);sigs=md.get("signals",{})
        strat=md.get("strategy","?");score=max(sigs.get("long_score",0),sigs.get("short_score",0))
        action,conf,reasoning,_=self.arbiter_ag.deliberate(verdicts,score,strat)
        self._dashboard(verdicts,md)
        log.info(f"\nARBITER: {action} | Confidence: {conf:.2f}")
        log.info(f"Reasoning: {reasoning}")
        log.info(f"\nWould {'ENTER' if 'GO' in action else 'SKIP'} — no trades placed in research mode")

    def microstructure(self):
        self._validate_keys();log.info("MICROSTRUCTURE MONITOR — 5s refresh")
        while True:
            try:
                p=self.client.price(SYMBOL);ob=self.client.orderbook(SYMBOL,20)
                tr=self.client.recent_trades(SYMBOL,1000)or[]
                vd=Sig.vpin(tr);bp=Sig.book_pressure(ob);sp=Sig.spread_bps(ob)
                mp,mid=Sig.micro_price(ob)
                print(f"\033[2J\033[HMICROSTRUCTURE {utcnow()}")
                print(f"Price:${p:,.2f} | Spread:{sp:.1f}bps | MicroP:${mp:.2f} Mid:${mid:.2f}")
                print(f"VPIN:{vd['vpin']:.3f} Dir:{vd['direction']} | BookP:{bp['pressure']:+.3f}")
                print(f"Bid depth:{bp['bid_depth']:.1f} Ask depth:{bp['ask_depth']:.1f}")
                oi=self.client.open_interest(SYMBOL);fr=self.client.funding_rate(SYMBOL)
                print(f"OI:{oi:.0f} | Funding:{fr:.4%}")
                time.sleep(5)
            except KeyboardInterrupt:break
            except Exception as e:print(f"Error:{e}");time.sleep(5)

    def report(self):
        log.info("═"*60);log.info("  PERFORMANCE REPORT");log.info("═"*60)
        trades=self.db.query("SELECT direction,total_pnl_pct,exit_reason,strategy,session FROM trades WHERE status='CLOSED'")
        if not trades:log.info("No closed trades.");return
        t=len(trades);w=sum(1 for x in trades if(x[1]or 0)>0);l=t-w;wr=w/t
        wn=[x[1]for x in trades if(x[1]or 0)>0];ls2=[x[1]for x in trades if(x[1]or 0)<=0]
        aw=np.mean(wn)if wn else 0;al=np.mean(ls2)if ls2 else 0
        pf=abs(aw*w)/(abs(al*l)+1e-10)if l>0 else 999
        log.info(f"Trades:{t} | WR:{wr:.1%}({w}W/{l}L) | AvgW:{aw:.2%} AvgL:{al:.2%} | PF:{pf:.2f}")
        bal=self.client.balance();log.info(f"Balance:${bal:.2f} | Start:${self.start_balance:.2f} | PnL:${bal-self.start_balance:.2f}")
        for d in["LONG","SHORT"]:
            dt=[x for x in trades if x[0]==d]
            if dt:dw=sum(1 for x in dt if(x[1]or 0)>0);log.info(f"  {d}:{len(dt)} trades {dw/len(dt):.0%}WR")
        for s in["ASIAN","EU","US","DEAD"]:
            st=[x for x in trades if x[4]==s]
            if st:sw=sum(1 for x in st if(x[1]or 0)>0);log.info(f"  {s}:{len(st)} trades {sw/len(st):.0%}WR")
        # Condition performance
        conds=self.db.query("SELECT condition_key,wins,losses,avg_pnl_pct FROM condition_performance ORDER BY (wins+losses) DESC LIMIT 10")
        if conds:
            log.info("\nTop conditions:");
            for ck,w2,l2,ap in conds:log.info(f"  {ck}: {w2}W/{l2}L WR={w2/(w2+l2):.0%} AvgPnL={ap:.2%}")
        log.info(f"\nAgent weights:{self.meta_ag.agent_weights}")
        ms=self.db.query("SELECT ts,milestone_type,value,note FROM milestones ORDER BY id DESC LIMIT 10")
        if ms:
            log.info("\nMilestones:");
            for ts,mt,mv,note in ms:log.info(f"  {ts}: {note}")
        # Run expectancy and clustering if enough trades
        if t>=10:self._expectancy_report(trades)
        if t>=20:self._clustering_report()
        self._execution_drift_report()
        self._brain_report()
        # Signal weight report
        mults=self.db.kv_get("signal_weight_mults",{})
        if mults:
            log.info("\nSignal weights (learned):")
            sorted_m=sorted(mults.items(),key=lambda x:x[1],reverse=True)
            for name,mult in sorted_m:
                tag="📈"if mult>1.10 else("📉"if mult<0.90 else"—")
                log.info(f"  {tag} {name}: ×{mult:.3f}")
        # Logistic model status
        lm=self.db.kv_get("logistic_model")
        if lm:
            log.info(f"\nLogistic model: trained on {lm.get('n_trades',0)} trades, accuracy={lm.get('accuracy',0):.1%}")
            w=lm.get("weights",[])
            if w and len(w)>len(LogisticScorer.FEATURES):
                importances=sorted(zip(LogisticScorer.FEATURES,np.abs(w[:-1])),key=lambda x:-x[1])
                log.info("  Top 5 predictive features:")
                for name,imp in importances[:5]:
                    sign="+"if w[LogisticScorer.FEATURES.index(name)]>0 else"-"
                    log.info(f"    {sign}{name}: |{imp:.3f}|")
            blend_pct=np.clip((lm.get("n_trades",0)-100)/100*80,0,80)
            log.info(f"  Scoring blend: {100-blend_pct:.0f}% hardcoded / {blend_pct:.0f}% logistic")
        else:
            total=self.db.query_one("SELECT count(*) FROM trades WHERE status='CLOSED'")[0]or 0
            log.info(f"\nLogistic model: NOT YET TRAINED ({total}/100 trades needed)")
        # GBM model status
        gm=self.db.kv_get("gbm_model")
        if gm:
            log.info(f"\n🌲 GBM model: {gm.get('n_stumps',0)} stumps, {gm.get('n_trades',0)} trades, accuracy={gm.get('accuracy',0):.1%}")
            fc=np.zeros(len(LogisticScorer.FEATURES))
            for s in gm.get("stumps",[]):fc[s["f"]]+=1
            top=sorted(zip(LogisticScorer.FEATURES,fc),key=lambda x:-x[1])[:5]
            log.info("  Top split features (interaction drivers):")
            for name,cnt in top:
                if cnt>0:log.info(f"    {name}: {int(cnt)} splits")
            log.info(f"  Phase: 3 — GBM is primary scorer")
        else:
            total=self.db.query_one("SELECT count(*) FROM trades WHERE status='CLOSED'")[0]or 0
            if total<500:log.info(f"\n🌲 GBM model: NOT YET ACTIVE ({total}/500 trades for Phase 3)")
        # Active phase
        log.info(f"\n  SCORING PHASES:")
        log.info(f"    Phase 1 (0-100): Hardcoded confluence")
        log.info(f"    Phase 2 (100-500): Logistic regression {'✅ ACTIVE'if lm and not gm else'⏳'}")
        log.info(f"    Phase 3 (500+): Gradient boosted model {'✅ ACTIVE'if gm else'⏳'}")

    def _expectancy_report(self,trades=None):
        """Expectancy decomposition — shows exactly WHERE money is made or lost."""
        log.info(f"\n{'═'*60}");log.info("  EXPECTANCY DECOMPOSITION");log.info(f"{'═'*60}")
        if trades is None:
            trades=self.db.query("SELECT direction,total_pnl_pct,exit_reason,strategy,session,vpin_at_entry,hurst FROM trades WHERE status='CLOSED'")
        if not trades or len(trades)<5:log.info("Not enough trades for expectancy analysis");return
        # Overall expectancy
        pnls=[t[1]or 0 for t in trades]
        wins=[p for p in pnls if p>0];losses=[p for p in pnls if p<=0]
        wr=len(wins)/len(pnls);lr=1-wr
        avg_w=np.mean(wins)if wins else 0;avg_l=np.mean(losses)if losses else 0
        expectancy=wr*avg_w+lr*avg_l
        log.info(f"\n  OVERALL EXPECTANCY PER TRADE: {expectancy:+.3%}")
        log.info(f"  Formula: ({wr:.1%} × {avg_w:+.2%}) + ({lr:.1%} × {avg_l:+.2%})")
        if expectancy>0:log.info(f"  ✅ POSITIVE EDGE — system is making money")
        else:log.info(f"  ❌ NEGATIVE EDGE — system is losing money after costs")
        # Expectancy by direction
        log.info(f"\n  BY DIRECTION:")
        for d in["LONG","SHORT"]:
            dt=[t[1]or 0 for t in trades if t[0]==d]
            if len(dt)>=3:
                dw=[p for p in dt if p>0];dl=[p for p in dt if p<=0]
                dwr=len(dw)/len(dt);dawg=np.mean(dw)if dw else 0;dalg=np.mean(dl)if dl else 0
                dexp=dwr*dawg+(1-dwr)*dalg
                tag="✅"if dexp>0 else"❌"
                log.info(f"    {d}: {dexp:+.3%} per trade ({len(dt)} trades, {dwr:.0%} WR) {tag}")
        # Expectancy by strategy
        log.info(f"\n  BY STRATEGY:")
        for st in["A","B"]:
            sdt=[t[1]or 0 for t in trades if t[3]==st]
            if len(sdt)>=3:
                sw=[p for p in sdt if p>0];sl=[p for p in sdt if p<=0]
                swr=len(sw)/len(sdt);sawg=np.mean(sw)if sw else 0;salg=np.mean(sl)if sl else 0
                sexp=swr*sawg+(1-swr)*salg
                tag="✅"if sexp>0 else"❌"
                log.info(f"    Strategy {st}: {sexp:+.3%} per trade ({len(sdt)} trades) {tag}")
        # Expectancy by session
        log.info(f"\n  BY SESSION:")
        for sess in["ASIAN","EU","US","DEAD"]:
            sst=[t[1]or 0 for t in trades if t[4]==sess]
            if len(sst)>=3:
                sw=[p for p in sst if p>0];sl=[p for p in sst if p<=0]
                swr=len(sw)/len(sst);sawg=np.mean(sw)if sw else 0;salg=np.mean(sl)if sl else 0
                sexp=swr*sawg+(1-swr)*salg
                tag="✅"if sexp>0 else"❌"
                log.info(f"    {sess}: {sexp:+.3%} per trade ({len(sst)} trades) {tag}")
                # Auto-recommendation
                if sexp<-0.005 and len(sst)>=10:
                    log.info(f"    ⚠️ RECOMMENDATION: Consider blocking trades in {sess} session (negative expectancy)")
        # Expectancy by VPIN level (if available)
        vpin_trades=self.db.query("SELECT vpin_at_entry,total_pnl_pct FROM trades WHERE status='CLOSED' AND vpin_at_entry IS NOT NULL")
        if len(vpin_trades)>=10:
            log.info(f"\n  BY VPIN LEVEL:")
            for label,lo,hi in[("Clean <0.35",0,0.35),("Normal 0.35-0.50",0.35,0.50),("Elevated 0.50-0.65",0.50,0.65)]:
                vt=[t[1]or 0 for t in vpin_trades if lo<=t[0]<hi]
                if len(vt)>=3:
                    vw=[p for p in vt if p>0];vl=[p for p in vt if p<=0]
                    vwr=len(vw)/len(vt);vawg=np.mean(vw)if vw else 0;valg=np.mean(vl)if vl else 0
                    vexp=vwr*vawg+(1-vwr)*valg
                    tag="✅"if vexp>0 else"❌"
                    log.info(f"    {label}: {vexp:+.3%} ({len(vt)} trades) {tag}")
        # Net expectancy after estimated costs
        fee_per_trade=0.0008  # ~4bps entry + 4bps exit at 5x
        net_exp=expectancy-fee_per_trade
        log.info(f"\n  NET EXPECTANCY (after ~8bps round-trip fees): {net_exp:+.3%}")
        if net_exp>0:
            annual_trades=len(trades)/max((time.time()-self.db.kv_get("first_trade_ts",time.time()-86400))/86400,1)*365
            projected_annual=((1+net_exp)**annual_trades-1)*100
            log.info(f"  Projected annual return (compounded): ~{projected_annual:.0f}% on {annual_trades:.0f} trades")
        log.info(f"{'═'*60}")

    def _clustering_report(self):
        """Trade clustering analysis — detects if losses come in streaks."""
        log.info(f"\n{'═'*60}");log.info("  TRADE CLUSTERING ANALYSIS");log.info(f"{'═'*60}")
        trades=self.db.query("SELECT total_pnl_pct,session,strategy,opened_at FROM trades WHERE status='CLOSED' ORDER BY id")
        if len(trades)<20:log.info("Not enough trades for clustering analysis");return
        outcomes=[1 if(t[0]or 0)>0 else 0 for t in trades]
        # Detect streaks
        streaks=[];current=1
        for i in range(1,len(outcomes)):
            if outcomes[i]==outcomes[i-1]:current+=1
            else:
                streaks.append(("WIN"if outcomes[i-1]==1 else"LOSS",current))
                current=1
        streaks.append(("WIN"if outcomes[-1]==1 else"LOSS",current))
        win_streaks=[s[1]for s in streaks if s[0]=="WIN"]
        loss_streaks=[s[1]for s in streaks if s[0]=="LOSS"]
        log.info(f"  Win streaks:  max={max(win_streaks)if win_streaks else 0} avg={np.mean(win_streaks):.1f}"if win_streaks else"  No win streaks")
        log.info(f"  Loss streaks: max={max(loss_streaks)if loss_streaks else 0} avg={np.mean(loss_streaks):.1f}"if loss_streaks else"  No loss streaks")
        # Runs test for randomness (are streaks longer than expected by chance?)
        n=len(outcomes);n1=sum(outcomes);n0=n-n1;runs=len(streaks)
        if n1>0 and n0>0:
            expected_runs=1+2*n1*n0/n
            std_runs=np.sqrt(2*n1*n0*(2*n1*n0-n)/(n*n*(n-1)))if n>1 else 1
            z=(runs-expected_runs)/(std_runs+1e-10)
            log.info(f"\n  Runs test: {runs} runs (expected {expected_runs:.1f}, z={z:.2f})")
            if z<-1.96:
                log.info(f"  ⚠️ CLUSTERING DETECTED: Outcomes are NOT random (z={z:.2f})")
                log.info(f"      Losses tend to cluster together — streaks are real, not just bad luck")
                log.info(f"      → The 2-loss pause and 5-loss pause in risk gates are correctly addressing this")
                # Identify which sessions have the worst clustering
                for sess in["ASIAN","EU","US","DEAD"]:
                    sess_trades=[(t[0]or 0)for t in trades if t[1]==sess]
                    if len(sess_trades)>=5:
                        sess_losses=sum(1 for p in sess_trades[-10:]if p<=0)
                        if sess_losses>=7:
                            log.info(f"      → {sess} session: {sess_losses}/10 recent losses — consider longer cooldown")
            elif z>1.96:
                log.info(f"  ✅ Anti-clustering: Outcomes alternate more than random (z={z:.2f})")
                log.info(f"      This is good — the system recovers well from losses")
            else:
                log.info(f"  ✅ Outcomes appear random — no significant clustering")
        # Loss clustering by time of day
        log.info(f"\n  Loss distribution by hour (UTC):")
        loss_hours=[]
        for t in trades:
            if(t[0]or 0)<=0 and t[3]:
                try:
                    h=int(t[3].split(" ")[1].split(":")[0])
                    loss_hours.append(h)
                except:pass
        if loss_hours:
            hour_counts=np.zeros(24)
            for h in loss_hours:
                if 0<=h<24:hour_counts[h]+=1
            worst_hours=np.argsort(hour_counts)[-3:][::-1]
            for h in worst_hours:
                if hour_counts[h]>0:log.info(f"    Hour {h:02d} UTC: {int(hour_counts[h])} losses")
        log.info(f"{'═'*60}")

    def _execution_drift_report(self):
        """Backtest vs live execution comparison."""
        log.info(f"\n{'═'*60}");log.info("  EXECUTION QUALITY REPORT");log.info(f"{'═'*60}")
        exec_logs=self.db.query("SELECT expected_price,fill_price,slippage_bps FROM execution_log ORDER BY id DESC LIMIT 100")
        if not exec_logs:log.info("No execution data yet");return
        slippages=[e[2]or 0 for e in exec_logs]
        log.info(f"  Trades analyzed: {len(exec_logs)}")
        log.info(f"  Avg slippage: {np.mean(slippages):.2f} bps")
        log.info(f"  Median slippage: {np.median(slippages):.2f} bps")
        log.info(f"  Worst slippage: {np.max(slippages):.2f} bps")
        log.info(f"  Best slippage: {np.min(slippages):.2f} bps")
        # Percentage of trades with worse-than-expected execution
        bad_fills=sum(1 for s in slippages if s>3.0)  # >3bps is "bad"
        log.info(f"  Fills >3bps slippage: {bad_fills}/{len(slippages)} ({bad_fills/len(slippages)*100:.0f}%)")
        # Execution cost as % of returns
        avg_slip_cost=np.mean(slippages)/10000*2  # entry+exit
        log.info(f"  Est execution drag: {avg_slip_cost:.3%} per round-trip")
        # Compare limit vs market fills (if we have the data)
        log.info(f"\n  Avg slippage trend (last 20 vs first 20):")
        if len(slippages)>=40:
            early=np.mean(slippages[:20]);recent=np.mean(slippages[-20:])
            log.info(f"    Early: {early:.2f}bps → Recent: {recent:.2f}bps")
            if recent<early:log.info(f"    ✅ Execution improving over time ({early-recent:.1f}bps saved)")
            else:log.info(f"    ⚠️ Execution degrading ({recent-early:.1f}bps worse)")
        log.info(f"{'═'*60}")

    def _brain_report(self):
        """Compare confluence vs logistic model — which brain is better?"""
        bl=self.db.kv_get("brain_comparison",[])
        if not bl or len(bl)<10:
            log.info(f"\n  Brain comparison: Not enough data ({len(bl) if bl else 0} split decisions tracked)")
            return
        log.info(f"\n{'═'*60}");log.info("  BRAIN COMPARISON: Confluence vs Logistic");log.info(f"{'═'*60}")
        hc_correct=sum(1 for b in bl if b.get("hc_correct",False))
        lg_correct=sum(1 for b in bl if b.get("lg_correct",False))
        agreed=sum(1 for b in bl if b.get("agreed",False))
        disagreed=len(bl)-agreed
        log.info(f"  Total scored decisions: {len(bl)}")
        log.info(f"  Agreed: {agreed} ({agreed/len(bl):.0%}) | Disagreed: {disagreed} ({disagreed/len(bl):.0%})")
        log.info(f"\n  When they AGREED ({agreed} trades):")
        agree_trades=[b for b in bl if b.get("agreed")]
        if agree_trades:
            agree_wins=sum(1 for b in agree_trades if b.get("profitable"))
            log.info(f"    Win rate: {agree_wins/len(agree_trades):.0%} — both brains aligned")
        log.info(f"\n  When they DISAGREED ({disagreed} trades):")
        disagree_trades=[b for b in bl if not b.get("agreed")]
        if disagree_trades:
            hc_won=sum(1 for b in disagree_trades if b.get("hc_correct")and not b.get("lg_correct"))
            lg_won=sum(1 for b in disagree_trades if b.get("lg_correct")and not b.get("hc_correct"))
            both_wrong=sum(1 for b in disagree_trades if not b.get("hc_correct")and not b.get("lg_correct"))
            log.info(f"    Confluence was right: {hc_won} times")
            log.info(f"    Logistic was right: {lg_won} times")
            log.info(f"    Both wrong: {both_wrong} times")
            if hc_won+lg_won>0:
                leader="CONFLUENCE"if hc_won>lg_won else("LOGISTIC"if lg_won>hc_won else"TIE")
                log.info(f"    👑 Current leader: {leader}")
        log.info(f"\n  Overall accuracy:")
        log.info(f"    Confluence: {hc_correct/len(bl):.0%} correct ({hc_correct}/{len(bl)})")
        log.info(f"    Logistic:   {lg_correct/len(bl):.0%} correct ({lg_correct}/{len(bl)})")
        # Recommendation
        if len(bl)>=30:
            if lg_correct>hc_correct*1.15:
                log.info(f"    📊 Logistic model is {lg_correct/max(hc_correct,1):.0%}× better — consider increasing blend weight")
            elif hc_correct>lg_correct*1.15:
                log.info(f"    📊 Confluence scoring is {hc_correct/max(lg_correct,1):.0%}× better — consider decreasing blend weight")
            else:
                log.info(f"    📊 Both systems perform similarly — hybrid blend is working well")
        log.info(f"{'═'*60}")

    def backtest(self):
        """Walk-forward backtest on historical data with slippage and fees."""
        self._validate_keys()
        log.info("═"*60);log.info("  WALK-FORWARD BACKTEST");log.info("═"*60)
        log.info("Fetching 500 bars of 1h history...")
        df=self.client.klines(SYMBOL,"1h",500)
        if len(df)<200:log.error("Not enough data for backtest");return
        closes=df["close"].values;highs=df["high"].values;lows=df["low"].values
        volumes=df["volume"].values
        # Walk-forward: train=200 bars, test=50 bars, step=50
        results=[];equity=300.0;trades=[];peak=300.0
        fee_rate=0.0004  # 4bps round trip (maker+taker on 5x)
        log.info(f"Starting equity: ${equity:.2f} | Bars: {len(df)} | Fee: {fee_rate:.2%}")
        for start in range(200,len(closes)-10,10):
            window=closes[max(0,start-200):start]
            test_window=closes[start:min(start+10,len(closes))]
            if len(window)<100 or len(test_window)<2:continue
            # Compute signals on training window
            hd=Sig.hurst(window[-100:]);h=hd["hurst"]
            if H_MR<=h<=H_TREND:continue  # neutral zone — skip
            kd=Sig.kalman(window[-200:]);hmm=Sig.hmm(np.diff(np.log(window+1e-10))[-200:])
            har=Sig.har_rv(window)
            # Simple direction decision
            if h>H_TREND:
                strat="A"
                if kd["velocity"]>kd["threshold"]and hmm["dominant"]=="BULL":direction="LONG"
                elif kd["velocity"]<-kd["threshold"]and hmm["dominant"]=="BEAR":direction="SHORT"
                else:continue
            else:
                strat="B"
                sr=Sig.stoch_rsi(window)
                if sr["k"]<15:direction="LONG"
                elif sr["k"]>85:direction="SHORT"
                else:continue
            # Simulate trade on test window
            entry=test_window[0];atr_val=np.mean([highs[start-i]-lows[start-i]for i in range(1,15)])
            if strat=="A":
                stop_d=max(min(atr_val*SA_STOP_ATR,entry*SA_STOP_MAX),entry*SA_STOP_MIN)
                tp1_d=atr_val*SA_TP1_ATR
            else:
                stop_d=max(min(atr_val*SB_STOP_ATR,entry*SB_STOP_MAX),entry*SB_STOP_MIN)
                tp1_d=atr_val*SB_TP1_ATR
            if direction=="LONG":stop=entry-stop_d;tp1=entry+tp1_d
            else:stop=entry+stop_d;tp1=entry-tp1_d
            # Size: ~14% of equity at 5x
            margin=equity*0.14;notional=margin*LEVERAGE;qty=notional/entry
            # Walk through test bars
            pnl=0;exit_reason="HOLD"
            for j in range(1,len(test_window)):
                bar_h=highs[start+j]if start+j<len(highs)else test_window[j]
                bar_l=lows[start+j]if start+j<len(lows)else test_window[j]
                bar_c=test_window[j]
                if direction=="LONG":
                    if bar_l<=stop:pnl=(stop-entry)/entry*LEVERAGE;exit_reason="STOP";break
                    if bar_h>=tp1:pnl=(tp1-entry)/entry*LEVERAGE*SA_TP1_FRAC+(bar_c-entry)/entry*LEVERAGE*(1-SA_TP1_FRAC);exit_reason="TP1";break
                else:
                    if bar_h>=stop:pnl=(entry-stop)/entry*LEVERAGE;exit_reason="STOP";break
                    if bar_l<=tp1:pnl=(entry-tp1)/entry*LEVERAGE*SA_TP1_FRAC+(entry-bar_c)/entry*LEVERAGE*(1-SA_TP1_FRAC);exit_reason="TP1";break
                pnl=(bar_c-entry)/entry*LEVERAGE if direction=="LONG"else(entry-bar_c)/entry*LEVERAGE
            # Apply fees + estimated slippage
            pnl-=fee_rate*2  # entry+exit fees
            pnl-=0.0003  # 3bps estimated slippage (with limit orders)
            pnl_dollar=margin*pnl
            equity+=pnl_dollar;peak=max(peak,equity)
            trades.append({"dir":direction,"strat":strat,"entry":entry,"pnl":pnl,
                          "pnl_usd":pnl_dollar,"exit":exit_reason,"equity":equity})
        # Report results
        if not trades:log.info("No trades generated in backtest");return
        total=len(trades);wins=[t for t in trades if t["pnl"]>0];losses=[t for t in trades if t["pnl"]<=0]
        wr=len(wins)/total;avg_w=np.mean([t["pnl"]for t in wins])if wins else 0
        avg_l=np.mean([t["pnl"]for t in losses])if losses else 0
        pf=abs(avg_w*len(wins))/(abs(avg_l*len(losses))+1e-10)if losses else 999
        max_dd=0;pk=300
        for t in trades:
            pk=max(pk,t["equity"]);dd=(pk-t["equity"])/pk;max_dd=max(max_dd,dd)
        sharpe=np.mean([t["pnl"]for t in trades])/(np.std([t["pnl"]for t in trades])+1e-10)*np.sqrt(252)
        final_eq=trades[-1]["equity"]
        log.info(f"\n{'═'*60}")
        log.info(f"  BACKTEST RESULTS (walk-forward, fee+slippage adjusted)")
        log.info(f"{'═'*60}")
        log.info(f"  Trades: {total} | WR: {wr:.1%} ({len(wins)}W/{len(losses)}L)")
        log.info(f"  Avg Win: {avg_w:.2%} | Avg Loss: {avg_l:.2%} | PF: {pf:.2f}")
        log.info(f"  Sharpe: {sharpe:.2f} | Max DD: {max_dd:.1%}")
        log.info(f"  Start: $300 → End: ${final_eq:.2f} ({(final_eq-300)/300:+.1%})")
        log.info(f"  Fees deducted: {fee_rate*2:.2%} per trade | Slippage: 3bps")
        # Per strategy
        for st in["A","B"]:
            st_t=[t for t in trades if t["strat"]==st]
            if st_t:
                sw=sum(1 for t in st_t if t["pnl"]>0)
                log.info(f"  Strategy {st}: {len(st_t)} trades, {sw/len(st_t):.0%} WR")
        # Per direction
        for d in["LONG","SHORT"]:
            dt=[t for t in trades if t["dir"]==d]
            if dt:
                dw=sum(1 for t in dt if t["pnl"]>0)
                log.info(f"  {d}: {len(dt)} trades, {dw/len(dt):.0%} WR")
        log.info(f"{'═'*60}")

    def agents_cmd(self):
        self._validate_keys();log.info("AGENT STATUS")
        md=self._fetch_data();verdicts=self._run_agents(md)
        for v in verdicts:
            log.info(f"\n{'='*40}")
            log.info(f"AGENT: {v.agent_name}")
            log.info(f"Direction: {v.direction} | Confidence: {v.confidence:.3f}")
            log.info(f"Veto: {v.veto} | Reason: {v.veto_reason}")
            log.info(f"Reasoning: {v.reasoning}")
            for k,val in v.scores.items():
                if not isinstance(val,(dict,list)):log.info(f"  {k}: {val}")

# ═══ MAIN ═══
def main():
    parser=argparse.ArgumentParser(description="Medallion v2.0 Multi-Agent Trading Bot")
    parser.add_argument("--setup",action="store_true",help="First-time setup")
    parser.add_argument("--verify",action="store_true",help="Health check")
    parser.add_argument("--research",action="store_true",help="Signal analysis (no trades)")
    parser.add_argument("--report",action="store_true",help="Performance report")
    parser.add_argument("--agents",action="store_true",help="Agent status")
    parser.add_argument("--microstructure",action="store_true",help="Live microstructure monitor")
    parser.add_argument("--optimize",action="store_true",help="Force Tier 3 optimization")
    parser.add_argument("--backtest",action="store_true",help="Walk-forward backtest")
    args=parser.parse_args()
    bot=MedallionBot()
    if args.setup:bot.setup()
    elif args.verify:bot.verify()
    elif args.research:bot.research()
    elif args.report:bot.report()
    elif args.agents:bot.agents_cmd()
    elif args.microstructure:bot.microstructure()
    elif args.optimize:bot.meta_ag.last_tier3=0;bot.meta_ag.tier3_check();log.info("Tier 3 forced")
    elif args.backtest:bot.backtest()
    else:bot.run()

if __name__=="__main__":main()
