const express = require('express');
const cors = require('cors');
const cron = require('node-cron');
const { createClient } = require('@supabase/supabase-js');

// ═══ CONFIG ═══
const PORT = process.env.PORT || 3001;
const SUPABASE_URL = process.env.SUPABASE_URL;
const SUPABASE_KEY = process.env.SUPABASE_SERVICE_KEY;
const supabase = SUPABASE_URL && SUPABASE_KEY ? createClient(SUPABASE_URL, SUPABASE_KEY) : null;

const PAIRS = ["BTCUSDT","ETHUSDT","BNBUSDT","SOLUSDT","XRPUSDT","DOGEUSDT","ADAUSDT","AVAXUSDT"];
const PL = {BTCUSDT:"BTC",ETHUSDT:"ETH",BNBUSDT:"BNB",SOLUSDT:"SOL",XRPUSDT:"XRP",DOGEUSDT:"DOGE",ADAUSDT:"ADA",AVAXUSDT:"AVAX"};
const TF_LABEL = {"1h":"1 hour","4h":"4 hour","1d":"Daily","1w":"Weekly"};

// ═══ INDICATOR MATH ═══
const ema=(d,p)=>{if(!d.length)return[];const k=2/(p+1);let e=d[0];return d.map(v=>(e=v*k+e*(1-k)));};
const sma=(d,p)=>d.map((_,i)=>{if(i<p-1)return null;let s=0;for(let j=i-p+1;j<=i;j++)s+=d[j];return s/p;});
function rsi(c,p=14){if(c.length<p+1)return Array(c.length).fill(50);const r=Array(c.length).fill(50);let ag=0,al=0;for(let i=1;i<=p;i++){const d=c[i]-c[i-1];if(d>0)ag+=d;else al-=d;}ag/=p;al/=p;r[p]=al===0?100:100-100/(1+ag/al);for(let i=p+1;i<c.length;i++){const d=c[i]-c[i-1];ag=(ag*(p-1)+(d>0?d:0))/p;al=(al*(p-1)+(d<0?-d:0))/p;r[i]=al===0?100:100-100/(1+ag/al);}return r;}
function bb(c,p=20,m=2){const s=sma(c,p);return s.map((v,i)=>{if(v===null)return{u:null,m:null,l:null};let sm=0;for(let j=i-p+1;j<=i;j++)sm+=(c[j]-v)**2;const sd=Math.sqrt(sm/p);return{u:v+m*sd,m:v,l:v-m*sd,sd};});}
function atr(cn,p=14){if(cn.length<2)return Array(cn.length).fill(0);const tr=cn.map((c,i)=>{if(i===0)return c.high-c.low;return Math.max(c.high-c.low,Math.abs(c.high-cn[i-1].close),Math.abs(c.low-cn[i-1].close));});return ema(tr,p);}
function adx(cn,p=14){if(cn.length<p*2)return{adx:Array(cn.length).fill(20),pDI:Array(cn.length).fill(25),mDI:Array(cn.length).fill(25)};const pDM=[],mDM=[],tr=[];for(let i=0;i<cn.length;i++){if(i===0){pDM.push(0);mDM.push(0);tr.push(cn[i].high-cn[i].low);continue;}const u=cn[i].high-cn[i-1].high,d=cn[i-1].low-cn[i].low;pDM.push(u>d&&u>0?u:0);mDM.push(d>u&&d>0?d:0);tr.push(Math.max(cn[i].high-cn[i].low,Math.abs(cn[i].high-cn[i-1].close),Math.abs(cn[i].low-cn[i-1].close)));}const a=ema(tr,p),sp=ema(pDM,p),sm2=ema(mDM,p);const pD=sp.map((v,i)=>a[i]?v/a[i]*100:0),mD=sm2.map((v,i)=>a[i]?v/a[i]*100:0);const dx=pD.map((v,i)=>{const s=v+mD[i];return s?Math.abs(v-mD[i])/s*100:0;});return{adx:ema(dx,p),pDI:pD,mDI:mD};}
function cci(cn,p=20){return cn.map((c,i)=>{if(i<p-1)return 0;const t=[];for(let j=i-p+1;j<=i;j++)t.push((cn[j].high+cn[j].low+cn[j].close)/3);const mn=t.reduce((a,b)=>a+b,0)/p;const md=t.reduce((a,b)=>a+Math.abs(b-mn),0)/p;return md?((c.high+c.low+c.close)/3-mn)/(0.015*md):0;});}
function macd(cl,f=12,s=26,sg=9){const ef=ema(cl,f),es=ema(cl,s);const line=ef.map((v,i)=>v-es[i]);const signal=ema(line,sg);const hist=line.map((v,i)=>v-signal[i]);return{line,signal,hist};}
function williamsR(cn,p=14){return cn.map((c,i)=>{if(i<p-1)return-50;let hh=-Infinity,ll=Infinity;for(let j=i-p+1;j<=i;j++){if(cn[j].high>hh)hh=cn[j].high;if(cn[j].low<ll)ll=cn[j].low;}return hh===ll?-50:(c.close-hh)/(hh-ll)*100;});}
function stochastic(cn,kp=14,dp=3){const rawK=cn.map((c,i)=>{if(i<kp-1)return 50;let hh=-Infinity,ll=Infinity;for(let j=i-kp+1;j<=i;j++){if(cn[j].high>hh)hh=cn[j].high;if(cn[j].low<ll)ll=cn[j].low;}return hh===ll?50:(c.close-ll)/(hh-ll)*100;});const k=sma(rawK.map(v=>v??50),dp).map(v=>v??50);const d=sma(k,dp).map(v=>v??50);return{k,d};}
function obv(cn){let o=0;return cn.map((c,i)=>{if(i===0)return 0;if(c.close>cn[i-1].close)o+=c.volume;else if(c.close<cn[i-1].close)o-=c.volume;return o;});}
function hullMA(cl,p=16){const wma1=ema(cl,Math.floor(p/2)),wma2=ema(cl,p);const diff=wma1.map((v,i)=>2*v-wma2[i]);return ema(diff,Math.floor(Math.sqrt(p)));}
function donchian(cn,p=20){return cn.map((c,i)=>{if(i<p-1)return{u:c.high,l:c.low,m:(c.high+c.low)/2};let hh=-Infinity,ll=Infinity;for(let j=i-p+1;j<=i;j++){if(cn[j].high>hh)hh=cn[j].high;if(cn[j].low<ll)ll=cn[j].low;}return{u:hh,l:ll,m:(hh+ll)/2};});}
function keltner(cn,cl,p=20,m=1.5){const mid=ema(cl,p),at=atr(cn,p);return mid.map((v,i)=>({u:v+m*at[i],l:v-m*at[i],m:v}));}
function vwap(cn){let cumPV=0,cumV=0;return cn.map(c=>{const tp=(c.high+c.low+c.close)/3;cumPV+=tp*c.volume;cumV+=c.volume;return cumV?cumPV/cumV:tp;});}
function ichimoku(cn,t=9,k=26,sb=52){const tenkan=cn.map((c,i)=>{if(i<t-1)return c.close;let hh=-Infinity,ll=Infinity;for(let j=i-t+1;j<=i;j++){if(cn[j].high>hh)hh=cn[j].high;if(cn[j].low<ll)ll=cn[j].low;}return(hh+ll)/2;});const kijun=cn.map((c,i)=>{if(i<k-1)return c.close;let hh=-Infinity,ll=Infinity;for(let j=i-k+1;j<=i;j++){if(cn[j].high>hh)hh=cn[j].high;if(cn[j].low<ll)ll=cn[j].low;}return(hh+ll)/2;});const spanA=tenkan.map((v,i)=>(v+kijun[i])/2);const spanB=cn.map((c,i)=>{if(i<sb-1)return c.close;let hh=-Infinity,ll=Infinity;for(let j=i-sb+1;j<=i;j++){if(cn[j].high>hh)hh=cn[j].high;if(cn[j].low<ll)ll=cn[j].low;}return(hh+ll)/2;});return{tenkan,kijun,spanA,spanB};}

// ═══ AGENT DEFINITIONS ═══
const AG={
  titan:{n:"Titan",i:"▲",c:"#60a5fa",tf:"4h",htf:"1d",s:"BB + EMA + RSI Hybrid"},
  phantom:{n:"Phantom",i:"▼",c:"#f87171",tf:"4h",htf:"1d",s:"Structural Short Seller"},
  reversal:{n:"Reversal",i:"☯",c:"#a78bfa",tf:"4h",htf:null,s:"Z-Score Mean Reversion"},
  shield:{n:"Shield",i:"🛡",c:"#94a3b8",tf:"4h",htf:null,s:"Portfolio Hedge Overlay"},
  razor:{n:"Razor",i:"⚡",c:"#fbbf24",tf:"1h",htf:"4h",s:"EMA Cross + RSI Scalp"},
  grokker:{n:"Grokker",i:"◑",c:"#34d399",tf:"4h",htf:"1d",s:"Multi-TF Contrarian"},
  breakout:{n:"Breakout",i:"💥",c:"#fb923c",tf:"4h",htf:"1d",s:"Structural Range Escape"},
  fortress:{n:"Fortress",i:"🏰",c:"#7dd3fc",tf:"1d",htf:"1w",s:"ADX Macro Trend"},
  comet:{n:"Comet",i:"☄",c:"#c084fc",tf:"1d",htf:null,s:"Smart Daily DCA"},
  pulse:{n:"Pulse",i:"📊",c:"#2dd4bf",tf:"4h",htf:null,s:"CCI Structural Cycles"},
  blitz:{n:"Blitz",i:"🎯",c:"#f472b6",tf:"1h",htf:"4h",s:"Structural Momentum"},
  // ═══ NEW AGENTS (17) ═══
  sensei:{n:"Sensei",i:"☯",c:"#e879f9",tf:"4h",htf:"1d",s:"Ichimoku Cloud Trend"},
  oracle:{n:"Oracle",i:"👁",c:"#a3e635",tf:"4h",htf:"1d",s:"OBV Volume Divergence"},
  viper:{n:"Viper",i:"🐍",c:"#22d3ee",tf:"4h",htf:null,s:"Bollinger/Keltner Squeeze"},
  voyager:{n:"Voyager",i:"🚀",c:"#818cf8",tf:"4h",htf:"1d",s:"Donchian Channel Breakout"},
  momentum:{n:"Momentum",i:"⚡",c:"#facc15",tf:"1h",htf:"4h",s:"RSI/EMA Fast Momentum"},
  glider:{n:"Glider",i:"🦅",c:"#86efac",tf:"4h",htf:"1d",s:"Hull MA Smooth Trend"},
  wraith:{n:"Wraith",i:"👻",c:"#c4b5fd",tf:"4h",htf:null,s:"Dual Oscillator (Williams+Stoch)"},
  needle:{n:"Needle",i:"🪡",c:"#fda4af",tf:"1h",htf:"4h",s:"Micro Pullback Scalp"},
  scalper:{n:"Scalper",i:"📈",c:"#67e8f9",tf:"1h",htf:null,s:"VWAP Bounce Scalp"},
  compass:{n:"Compass",i:"🧭",c:"#d8b4fe",tf:"4h",htf:null,s:"Pair Relative Rotation"},
  vertex:{n:"Vertex",i:"⚙️",c:"#fca5a5",tf:"1h",htf:null,s:"Order Book Spread Capture"},
  flash:{n:"Flash",i:"⚡",c:"#bef264",tf:"1h",htf:null,s:"Impulse Momentum Ride"},
  surge:{n:"Surge",i:"🔥",c:"#fdba74",tf:"1h",htf:null,s:"Order Flow Pressure"},
  abyss:{n:"Abyss",i:"🌊",c:"#6366f1",tf:"4h",htf:"1d",s:"Capitulation Bottom-Buyer"},
  specter:{n:"Specter",i:"👤",c:"#a1a1aa",tf:"4h",htf:null,s:"Stealth Momentum (OI Divergence)"},
  trend_rider:{n:"Trend Rider",i:"🏄",c:"#f59e0b",tf:"4h",htf:"1d",s:"MACD Trend Following"},
  flicker:{n:"Flicker",i:"✨",c:"#ec4899",tf:"4h",htf:null,s:"Spread / Pair Arbitrage"},
};

// ═══ SIGNAL FUNCTIONS ═══
function sigTitan(cn,cl,hCn,hCl){const n=cl.length-1;if(n<50)return{s:"HOLD",c:0,r:"Warming up (need 50× 4h)",ind:{}};const b=bb(cl),e50=ema(cl,50),rs=rsi(cl),at=atr(cn);const bn=b[n];if(!bn?.m)return{s:"HOLD",c:0,r:"BB loading",ind:{}};let hB="neutral";if(hCl?.length>20){const he=ema(hCl,20),hr=rsi(hCl);hB=hCl[hCl.length-1]>he[he.length-1]&&hr[hr.length-1]>45?"bullish":hCl[hCl.length-1]<he[he.length-1]&&hr[hr.length-1]<55?"bearish":"neutral";}const ind={RSI_4h:rs[n].toFixed(1),EMA50:e50[n].toFixed(2),BB_L:bn.l.toFixed(2),BB_U:bn.u.toFixed(2),ATR:at[n].toFixed(2),Daily:hB};if(cl[n]<=bn.l&&cl[n]>e50[n]&&rs[n]<40&&rs[n]>rs[n-1]&&hB!=="bearish")return{s:"LONG",c:hB==="bullish"?.85:.65,r:`4h: Price ${cl[n].toFixed(2)} at BB lower, above EMA50. RSI ${rs[n].toFixed(1)} oversold turning up. Daily: ${hB}.`,sl:cl[n]-1.5*at[n],tp:bn.m,ind};if(cl[n]>=bn.u&&cl[n]<e50[n]&&rs[n]>60&&rs[n]<rs[n-1]&&hB!=="bullish")return{s:"SHORT",c:hB==="bearish"?.85:.65,r:`4h: BB upper below EMA50. RSI ${rs[n].toFixed(1)} overbought. Daily: ${hB}.`,sl:cl[n]+1.5*at[n],tp:bn.m,ind};return{s:"HOLD",c:0,r:`4h mid-band, RSI ${rs[n].toFixed(1)}. Daily: ${hB}. No setup.`,ind};}
function sigPhantom(cn,cl,hCn,hCl){const n=cl.length-1;if(n<50)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const e9=ema(cl,9),e21=ema(cl,21),e50=ema(cl,50),rs=rsi(cl),at=atr(cn);let dB=false;if(hCl?.length>50){const he=ema(hCl,50);dB=hCl[hCl.length-1]<he[he.length-1];}const ind={RSI_4h:rs[n].toFixed(1),EMA9:e9[n].toFixed(2),EMA21:e21[n].toFixed(2),Daily_Bear:dB?"Yes":"No"};if(e9[n]<e21[n]&&cl[n]<e50[n]&&rs[n]<45&&dB){const h3=cn.slice(-3).map(c=>c.high);if(Math.max(...h3)>e21[n]&&cl[n]<e21[n])return{s:"SHORT",c:.8,r:`STRUCTURAL SHORT — 4h failed bounce at EMA21. Daily confirms downtrend. RSI ${rs[n].toFixed(1)}.`,sl:e21[n]+at[n],tp:cl[n]-2*at[n],ind};return{s:"SHORT",c:.7,r:`4h bearish + daily down. EMA9<21<50. RSI ${rs[n].toFixed(1)}.`,sl:e50[n],tp:cl[n]-1.5*at[n],ind};}if(e9[n]<e21[n]&&!dB)return{s:"HOLD",c:0,r:`4h bearish but daily NOT confirming. Waiting.`,ind};return{s:"HOLD",c:0,r:`No bearish structure. 4h: ${e9[n]>e21[n]?"bull":"mixed"}.`,ind};}
function sigReversal(cn,cl){const n=cl.length-1;if(n<50)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const sm=sma(cl,50);if(!sm[n])return{s:"HOLD",c:0,r:"SMA loading",ind:{}};let sum=0;for(let i=n-49;i<=n;i++)sum+=(cl[i]-sm[n])**2;const sd=Math.sqrt(sum/50);if(!sd)return{s:"HOLD",c:0,r:"No vol",ind:{}};const z=(cl[n]-sm[n])/sd,pz=n>0?(cl[n-1]-(sm[n-1]||sm[n]))/(sd||1):z;const ind={Z_4h:z.toFixed(2),SMA50:sm[n].toFixed(2)};if(z<-2&&z>pz)return{s:"LONG",c:Math.min(1,Math.abs(z)/3),r:`4h Z-score ${z.toFixed(2)} — ${Math.abs(z).toFixed(1)}σ below mean. Reverting up.`,sl:sm[n]-3*sd,tp:sm[n],ind};if(z>2&&z<pz)return{s:"SHORT",c:Math.min(1,Math.abs(z)/3),r:`4h Z-score ${z.toFixed(2)} — overextended, reverting.`,sl:sm[n]+3*sd,tp:sm[n],ind};return{s:"HOLD",c:0,r:`Z ${z.toFixed(2)} within ±2.`,ind};}
function sigRazor(cn,cl,hCn,hCl){const n=cl.length-1;if(n<20)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const e5=ema(cl,5),e13=ema(cl,13),rs=rsi(cl,9),at=atr(cn);let hT="neutral";if(hCl?.length>21){const he=ema(hCl,21);hT=he[he.length-1]>he[he.length-2]?"up":"down";}const ind={EMA5:e5[n].toFixed(2),EMA13:e13[n].toFixed(2),RSI9:rs[n].toFixed(1),"4h":hT};if(n>0&&e5[n]>e13[n]&&e5[n-1]<=e13[n-1]&&rs[n]>50&&rs[n]<75&&hT==="up")return{s:"LONG",c:.75,r:`1h bull cross. RSI ${rs[n].toFixed(1)}. 4h UP — aligned.`,sl:cl[n]-at[n],tp:cl[n]+1.5*at[n],ind};if(n>0&&e5[n]<e13[n]&&e5[n-1]>=e13[n-1]&&rs[n]<50&&rs[n]>25&&hT==="down")return{s:"SHORT",c:.75,r:`1h bear cross. 4h DOWN.`,sl:cl[n]+at[n],tp:cl[n]-1.5*at[n],ind};return{s:"HOLD",c:0,r:`No 1h cross. 4h: ${hT}.`,ind};}
function sigBreakout(cn,cl,hCn,hCl){const n=cl.length-1;if(n<25)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const hi=cn.slice(n-20,n).map(c=>c.high),lo=cn.slice(n-20,n).map(c=>c.low);const up=Math.max(...hi),low=Math.min(...lo);const at2=atr(cn),vol=cn[n].volume,avgV=cn.slice(n-20,n).reduce((a,c)=>a+c.volume,0)/20,vr=(vol/avgV).toFixed(1);let dR=true;if(hCl?.length>20){const dhi=Math.max(...hCn.slice(-20).map(c=>c.high));dR=cl[n]<dhi*.99;}const ind={"4h_Hi":up.toFixed(2),"4h_Lo":low.toFixed(2),Vol:vr+"×"};if(cl[n]>up&&vol>avgV*1.3&&at2[n]>at2[n-1]&&dR)return{s:"LONG",c:.7,r:`4h BREAKOUT above ${up.toFixed(2)}. Vol ${vr}×. Daily has room.`,sl:up-.5*at2[n],tp:cl[n]+(up-low),ind};if(cl[n]<low&&vol>avgV*1.3&&at2[n]>at2[n-1])return{s:"SHORT",c:.7,r:`4h breakdown below ${low.toFixed(2)}. Vol ${vr}×.`,sl:low+.5*at2[n],tp:cl[n]-(up-low),ind};return{s:"HOLD",c:0,r:`In range [${low.toFixed(2)}-${up.toFixed(2)}].`,ind};}
function sigFortress(cn,cl,hCn,hCl){const n=cl.length-1;if(n<30)return{s:"HOLD",c:0,r:"Warming up (30 daily = ~1 month)",ind:{}};const{adx:ax,pDI,mDI}=adx(cn);const e50=ema(cl,50),at2=atr(cn);let wk=false;if(hCl?.length>20){const we=ema(hCl,20);wk=hCl[hCl.length-1]>we[we.length-1];}const ind={ADX:ax[n].toFixed(1),"+DI":pDI[n].toFixed(1),"-DI":mDI[n].toFixed(1),Weekly:wk?"Bull":"No"};if(ax[n]>25&&pDI[n]>mDI[n]&&cl[n]>e50[n]&&ax[n]>ax[n-1]&&wk)return{s:"LONG",c:Math.min(1,ax[n]/50),r:`MACRO TREND. Daily ADX ${ax[n].toFixed(1)} rising. Weekly confirms.`,sl:cl[n]-2*at2[n],tp:cl[n]+3*at2[n],ind};if(ax[n]>25&&mDI[n]>pDI[n]&&cl[n]<e50[n]&&ax[n]>ax[n-1])return{s:"SHORT",c:Math.min(1,ax[n]/50),r:`Daily downtrend: ADX ${ax[n].toFixed(1)}, -DI dominates.`,sl:cl[n]+2*at2[n],tp:cl[n]-3*at2[n],ind};return{s:"HOLD",c:0,r:`ADX ${ax[n].toFixed(1)} — ${ax[n]<25?"weak":"misaligned"}. Weekly: ${wk?"bull":"no"}.`,ind};}
function sigPulse(cn,cl){const n=cl.length-1;if(n<25)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const cc=cci(cn),e50=ema(cl,50),sl=e50[n]-e50[Math.max(0,n-3)],at2=atr(cn);const ind={CCI:cc[n].toFixed(0),Slope:sl>0?"Up":"Down"};if(cc[n]>-100&&cc[n-1]<=-100&&sl>0)return{s:"LONG",c:.65,r:`4h CCI above -100. Cycle turning bull.`,sl:cl[n]-1.5*at2[n],tp:cl[n]+2*at2[n],ind};if(cc[n]<100&&cc[n-1]>=100&&sl<0)return{s:"SHORT",c:.65,r:`4h CCI below +100. Cycle turning bear.`,sl:cl[n]+1.5*at2[n],tp:cl[n]-2*at2[n],ind};return{s:"HOLD",c:0,r:`CCI ${cc[n].toFixed(0)} — no transition.`,ind};}
function sigGrokker(cn,cl,hCn,hCl){const n=cl.length-1;if(n<20)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const rs=rsi(cl),vol=cn[n].volume,avgV=cn.slice(Math.max(0,n-20),n).reduce((a,c)=>a+c.volume,0)/20,vr=(vol/avgV).toFixed(1),at2=atr(cn);let dRSI=50;if(hCl?.length>14){const dr=rsi(hCl);dRSI=dr[dr.length-1];}const ind={RSI_4h:rs[n].toFixed(1),RSI_D:dRSI.toFixed(1),Vol:vr+"×"};if(rs[n]<25&&vol>avgV*1.5&&rs[n]>rs[n-1]&&dRSI<35)return{s:"LONG",c:.8,r:`MULTI-TF FEAR — 4h RSI ${rs[n].toFixed(1)} + Daily ${dRSI.toFixed(1)}. Contrarian buy.`,sl:cl[n]-2*at2[n],tp:cl[n]+2.5*at2[n],ind};if(rs[n]>75&&vol>avgV*1.5&&rs[n]<rs[n-1]&&dRSI>65)return{s:"SHORT",c:.8,r:`MULTI-TF GREED — fading euphoria.`,sl:cl[n]+2*at2[n],tp:cl[n]-2.5*at2[n],ind};return{s:"HOLD",c:0,r:`4h RSI ${rs[n].toFixed(1)}, Daily ${dRSI.toFixed(1)}. Need both extreme.`,ind};}
function sigComet(cn,cl,_h,_hc,tick){const n=cl.length-1;if(n<14)return{s:"HOLD",c:0,r:"Warming up",ind:{}};if(tick%10!==0)return{s:"HOLD",c:0,r:`DCA: ${10-tick%10} cycles to next buy`,ind:{}};const rs=rsi(cl);let m=1;if(rs[n]<30)m=1.5;else if(rs[n]<40)m=1.25;else if(rs[n]>70)m=.5;else if(rs[n]>60)m=.75;return{s:"LONG",c:.3*m,r:`Daily DCA. RSI ${rs[n].toFixed(1)} → ${m}×.`,ind:{RSI:rs[n].toFixed(1),Mult:m+"×"}};}
function sigBlitz(cn,cl,hCn,hCl){const n=cl.length-1;if(n<10)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const vol=cn[n].volume,avgV=cn.slice(Math.max(0,n-10),n).reduce((a,c)=>a+c.volume,0)/10,vr=(vol/avgV).toFixed(1);const roc=(cl[n]-cl[Math.max(0,n-5)])/cl[Math.max(0,n-5)]*100;const body=Math.abs(cn[n].close-cn[n].open)/(cn[n].high-cn[n].low||1);let hUp=false;if(hCl?.length>21){const he=ema(hCl,21);hUp=he[he.length-1]>he[he.length-2];}const ind={Vol:vr+"×",ROC:roc.toFixed(2)+"%","4h":hUp?"Up":"Down"};if(vol>avgV*3&&roc>2&&roc<10&&body>.6&&hUp)return{s:"LONG",c:.65,r:`1h momentum + 4h up. Vol ${vr}×.`,sl:cl[n]*.97,tp:cl[n]*1.05,ind};return{s:"HOLD",c:0,r:`No momentum. Vol ${vr}×, ROC ${roc.toFixed(2)}%.`,ind};}
// ═══ NEW SIGNAL FUNCTIONS (17 agents) ═══
function sigSensei(cn,cl,hCn,hCl){const n=cl.length-1;if(n<52)return{s:"HOLD",c:0,r:"Warming up (need 52× 4h)",ind:{}};const ich=ichimoku(cn);const at=atr(cn);const t=ich.tenkan[n],k=ich.kijun[n],sa=ich.spanA[n],sb=ich.spanB[n];const cloudTop=Math.max(sa,sb),cloudBot=Math.min(sa,sb);let dB="neutral";if(hCl?.length>52){const di=ichimoku(hCn);dB=hCl[hCl.length-1]>Math.max(di.spanA[hCl.length-1],di.spanB[hCl.length-1])?"bullish":"bearish";}const ind={Tenkan:t.toFixed(2),Kijun:k.toFixed(2),Cloud:`${cloudBot.toFixed(0)}-${cloudTop.toFixed(0)}`,Daily:dB};if(cl[n]>cloudTop&&t>k&&t>ich.tenkan[n-1]&&dB!=="bearish")return{s:"LONG",c:dB==="bullish"?.8:.6,r:`Above cloud. Tenkan>${k.toFixed(0)} Kijun. Daily: ${dB}.`,sl:k-at[n],tp:cl[n]+2*at[n],ind};if(cl[n]<cloudBot&&t<k&&t<ich.tenkan[n-1]&&dB!=="bullish")return{s:"SHORT",c:dB==="bearish"?.8:.6,r:`Below cloud. Tenkan<Kijun. Daily: ${dB}.`,sl:k+at[n],tp:cl[n]-2*at[n],ind};return{s:"HOLD",c:0,r:`${cl[n]>cloudBot&&cl[n]<cloudTop?"In cloud":"No setup"}. Daily: ${dB}.`,ind};}

function sigOracle(cn,cl,hCn,hCl){const n=cl.length-1;if(n<30)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const ob=obv(cn),e20=ema(cl,20),at=atr(cn);const obvEma=ema(ob,20);const priceSlope=(cl[n]-cl[Math.max(0,n-10)])/cl[Math.max(0,n-10)]*100;const obvSlope=(ob[n]-ob[Math.max(0,n-10)])/(Math.abs(ob[Math.max(0,n-10)])||1)*100;let dB="neutral";if(hCl?.length>20){const hr=rsi(hCl);dB=hr[hr.length-1]>55?"bullish":hr[hr.length-1]<45?"bearish":"neutral";}const ind={OBV_slope:obvSlope.toFixed(1)+"%",Price_slope:priceSlope.toFixed(1)+"%",Daily:dB};if(obvSlope>5&&priceSlope<1&&ob[n]>obvEma[n]&&dB!=="bearish")return{s:"LONG",c:.7,r:`OBV divergence: volume accumulating (${obvSlope.toFixed(1)}%) while price flat (${priceSlope.toFixed(1)}%).`,sl:cl[n]-1.5*at[n],tp:cl[n]+2*at[n],ind};if(obvSlope<-5&&priceSlope>-1&&ob[n]<obvEma[n]&&dB!=="bullish")return{s:"SHORT",c:.7,r:`OBV divergence: distribution (${obvSlope.toFixed(1)}%) while price holds.`,sl:cl[n]+1.5*at[n],tp:cl[n]-2*at[n],ind};return{s:"HOLD",c:0,r:`No OBV divergence. OBV ${obvSlope.toFixed(1)}%, Price ${priceSlope.toFixed(1)}%.`,ind};}

function sigViper(cn,cl){const n=cl.length-1;if(n<25)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const b=bb(cl),k=keltner(cn,cl),at=atr(cn),rs=rsi(cl);const bn=b[n],kn=k[n];if(!bn?.u||!kn?.u)return{s:"HOLD",c:0,r:"Indicators loading",ind:{}};const squeeze=bn.u<kn.u&&bn.l>kn.l;let prevSq=false;if(n>0){const bp=b[n-1],kp=k[n-1];prevSq=bp?.u<kp?.u&&bp?.l>kp?.l;}const ind={Squeeze:squeeze?"YES":"no",BB_W:(bn.u-bn.l).toFixed(2),KC_W:(kn.u-kn.l).toFixed(2),RSI:rs[n].toFixed(1)};if(!squeeze&&prevSq&&cl[n]>bn.m&&rs[n]>50)return{s:"LONG",c:.75,r:`Squeeze FIRED UP. BB expanded above Keltner. RSI ${rs[n].toFixed(1)}.`,sl:bn.m-at[n],tp:cl[n]+2.5*at[n],ind};if(!squeeze&&prevSq&&cl[n]<bn.m&&rs[n]<50)return{s:"SHORT",c:.75,r:`Squeeze FIRED DOWN. Breakdown confirmed.`,sl:bn.m+at[n],tp:cl[n]-2.5*at[n],ind};return{s:"HOLD",c:0,r:`${squeeze?"Squeeze active — waiting for fire":"No squeeze"}. RSI ${rs[n].toFixed(1)}.`,ind};}

function sigVoyager(cn,cl,hCn,hCl){const n=cl.length-1;if(n<25)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const dc=donchian(cn),at=atr(cn);const vol=cn[n].volume,avgV=cn.slice(Math.max(0,n-20),n).reduce((a,c)=>a+c.volume,0)/20;let dB=true;if(hCl?.length>20){const dhi=Math.max(...hCn.slice(-20).map(c=>c.high));dB=cl[n]<dhi*.99;}const ind={DC_Hi:dc[n].u.toFixed(2),DC_Lo:dc[n].l.toFixed(2),Vol:(vol/avgV).toFixed(1)+"×"};if(cl[n]>=dc[n].u&&vol>avgV*1.2&&dB)return{s:"LONG",c:.7,r:`Donchian breakout above ${dc[n].u.toFixed(2)}. Vol ${(vol/avgV).toFixed(1)}×.`,sl:dc[n].m,tp:cl[n]+2*(dc[n].u-dc[n].l),ind};if(cl[n]<=dc[n].l&&vol>avgV*1.2)return{s:"SHORT",c:.7,r:`Donchian breakdown below ${dc[n].l.toFixed(2)}.`,sl:dc[n].m,tp:cl[n]-2*(dc[n].u-dc[n].l),ind};return{s:"HOLD",c:0,r:`In channel [${dc[n].l.toFixed(0)}-${dc[n].u.toFixed(0)}].`,ind};}

function sigMomentum(cn,cl,hCn,hCl){const n=cl.length-1;if(n<20)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const rs=rsi(cl,14),e9=ema(cl,9),e21=ema(cl,21),at=atr(cn);const roc=(cl[n]-cl[Math.max(0,n-5)])/cl[Math.max(0,n-5)]*100;let hT="neutral";if(hCl?.length>21){const he=ema(hCl,21);hT=he[he.length-1]>he[he.length-2]?"up":"down";}const ind={RSI:rs[n].toFixed(1),ROC:roc.toFixed(2)+"%","4h":hT};if(rs[n]>55&&rs[n]<75&&e9[n]>e21[n]&&roc>1&&hT==="up")return{s:"LONG",c:.7,r:`Momentum LONG — RSI ${rs[n].toFixed(1)}, ROC ${roc.toFixed(1)}%. 4h up.`,sl:cl[n]-1.2*at[n],tp:cl[n]+1.8*at[n],ind};if(rs[n]<45&&rs[n]>25&&e9[n]<e21[n]&&roc<-1&&hT==="down")return{s:"SHORT",c:.7,r:`Momentum SHORT — RSI ${rs[n].toFixed(1)}, ROC ${roc.toFixed(1)}%. 4h down.`,sl:cl[n]+1.2*at[n],tp:cl[n]-1.8*at[n],ind};return{s:"HOLD",c:0,r:`No momentum. RSI ${rs[n].toFixed(1)}, ROC ${roc.toFixed(2)}%.`,ind};}

function sigGlider(cn,cl,hCn,hCl){const n=cl.length-1;if(n<20)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const hull=hullMA(cl,16),at=atr(cn);const hSlope=hull[n]-hull[Math.max(0,n-3)];let dB="neutral";if(hCl?.length>20){const dh=hullMA(hCl,16);dB=dh[dh.length-1]>dh[Math.max(0,dh.length-4)]?"bullish":"bearish";}const ind={Hull:hull[n].toFixed(2),Slope:hSlope>0?"Up":"Down",Daily:dB};if(hSlope>0&&cl[n]>hull[n]&&n>0&&(hull[n-1]<=hull[n-2]||cl[n-1]<=hull[n-1])&&dB!=="bearish")return{s:"LONG",c:dB==="bullish"?.75:.6,r:`Hull MA turning up. Price above ${hull[n].toFixed(0)}. Daily: ${dB}.`,sl:hull[n]-at[n],tp:cl[n]+2*at[n],ind};if(hSlope<0&&cl[n]<hull[n]&&n>0&&(hull[n-1]>=hull[n-2]||cl[n-1]>=hull[n-1])&&dB!=="bullish")return{s:"SHORT",c:dB==="bearish"?.75:.6,r:`Hull MA turning down. Daily: ${dB}.`,sl:hull[n]+at[n],tp:cl[n]-2*at[n],ind};return{s:"HOLD",c:0,r:`Hull ${hSlope>0?"up":"down"}, no fresh cross. Daily: ${dB}.`,ind};}

function sigWraith(cn,cl){const n=cl.length-1;if(n<20)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const wr=williamsR(cn),st=stochastic(cn),e21=ema(cl,21),at=atr(cn);const ind={WR:wr[n].toFixed(1),StK:st.k[n].toFixed(1),StD:st.d[n].toFixed(1)};if(wr[n]<-80&&st.k[n]<20&&st.d[n]<20&&n>0&&st.k[n]>st.d[n]&&st.k[n-1]<=st.d[n-1]&&wr[n]>wr[n-1]&&cl[n]>e21[n])return{s:"LONG",c:.8,r:`DUAL OVERSOLD — WR ${wr[n].toFixed(0)} + Stoch ${st.k[n].toFixed(0)}/${st.d[n].toFixed(0)} bullish cross.`,sl:cl[n]-1.5*at[n],tp:cl[n]+2*at[n],ind};if(wr[n]>-20&&st.k[n]>80&&st.d[n]>80&&n>0&&st.k[n]<st.d[n]&&st.k[n-1]>=st.d[n-1]&&wr[n]<wr[n-1]&&cl[n]<e21[n])return{s:"SHORT",c:.8,r:`DUAL OVERBOUGHT — WR ${wr[n].toFixed(0)} + Stoch bearish cross.`,sl:cl[n]+1.5*at[n],tp:cl[n]-2*at[n],ind};return{s:"HOLD",c:0,r:`WR ${wr[n].toFixed(0)}, Stoch ${st.k[n].toFixed(0)}. Need dual extreme + cross.`,ind};}

function sigNeedle(cn,cl,hCn,hCl){const n=cl.length-1;if(n<20)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const e9=ema(cl,9),e21=ema(cl,21),rs=rsi(cl,7),at=atr(cn);let hT="neutral";if(hCl?.length>21){const he=ema(hCl,21);hT=he[he.length-1]>he[he.length-2]?"up":"down";}const ind={RSI7:rs[n].toFixed(1),EMA9:e9[n].toFixed(2),"4h":hT};if(e9[n]>e21[n]&&rs[n]<35&&rs[n]>rs[n-1]&&hT==="up"){const pb=(e9[n]-cl[n])/at[n];if(pb>0.3&&pb<1.5)return{s:"LONG",c:.7,r:`1h micro pullback in uptrend. RSI7 ${rs[n].toFixed(1)} bouncing. 4h UP.`,sl:cl[n]-at[n],tp:e9[n]+.5*at[n],ind};}if(e9[n]<e21[n]&&rs[n]>65&&rs[n]<rs[n-1]&&hT==="down"){const pb=(cl[n]-e9[n])/at[n];if(pb>0.3&&pb<1.5)return{s:"SHORT",c:.7,r:`1h micro bounce in downtrend. RSI7 ${rs[n].toFixed(1)} fading. 4h DOWN.`,sl:cl[n]+at[n],tp:e9[n]-.5*at[n],ind};}return{s:"HOLD",c:0,r:`No pullback setup. RSI7 ${rs[n].toFixed(1)}. 4h: ${hT}.`,ind};}

function sigScalper(cn,cl){const n=cl.length-1;if(n<20)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const vw=vwap(cn),rs=rsi(cl,9),at=atr(cn);const dist=(cl[n]-vw[n])/vw[n]*100;const ind={VWAP:vw[n].toFixed(2),Dist:dist.toFixed(2)+"%",RSI9:rs[n].toFixed(1)};if(dist<-0.3&&dist>-2&&rs[n]<40&&rs[n]>rs[n-1])return{s:"LONG",c:.65,r:`VWAP bounce — ${dist.toFixed(2)}% below VWAP. RSI9 ${rs[n].toFixed(1)} turning.`,sl:vw[n]-1.5*at[n],tp:vw[n],ind};if(dist>0.3&&dist<2&&rs[n]>60&&rs[n]<rs[n-1])return{s:"SHORT",c:.65,r:`VWAP rejection — ${dist.toFixed(2)}% above. RSI9 fading.`,sl:vw[n]+1.5*at[n],tp:vw[n],ind};return{s:"HOLD",c:0,r:`VWAP dist ${dist.toFixed(2)}%. Need ±0.3-2% zone + RSI turn.`,ind};}

function sigCompass(cn,cl){const n=cl.length-1;if(n<30)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const rs=rsi(cl,14),e20=ema(cl,20);const perf5=(cl[n]-cl[Math.max(0,n-5)])/cl[Math.max(0,n-5)]*100;const perf20=(cl[n]-cl[Math.max(0,n-20)])/cl[Math.max(0,n-20)]*100;const at=atr(cn);const ind={Perf5d:perf5.toFixed(2)+"%",Perf20d:perf20.toFixed(2)+"%",RSI:rs[n].toFixed(1)};if(perf20<-5&&perf5>1&&rs[n]>45&&rs[n]<60&&cl[n]>e20[n])return{s:"LONG",c:.65,r:`Rotation: 20d weak (${perf20.toFixed(1)}%) but 5d reversing (${perf5.toFixed(1)}%). RSI ${rs[n].toFixed(1)}.`,sl:cl[n]-1.5*at[n],tp:cl[n]+2*at[n],ind};if(perf20>5&&perf5<-1&&rs[n]<55&&rs[n]>40&&cl[n]<e20[n])return{s:"SHORT",c:.65,r:`Rotation: 20d strong but 5d fading. Mean reversion play.`,sl:cl[n]+1.5*at[n],tp:cl[n]-2*at[n],ind};return{s:"HOLD",c:0,r:`No rotation signal. 5d: ${perf5.toFixed(1)}%, 20d: ${perf20.toFixed(1)}%.`,ind};}

function sigVertex(cn,cl){const n=cl.length-1;if(n<15)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const at=atr(cn);const spread=(cn[n].high-cn[n].low)/cl[n]*100;const avgSpread=cn.slice(Math.max(0,n-20),n).reduce((a,c)=>a+(c.high-c.low)/c.close*100,0)/20;const vol=cn[n].volume,avgV=cn.slice(Math.max(0,n-20),n).reduce((a,c)=>a+c.volume,0)/20;const body=Math.abs(cn[n].close-cn[n].open)/(cn[n].high-cn[n].low||1);const ind={Spread:spread.toFixed(3)+"%",AvgSpread:avgSpread.toFixed(3)+"%",Vol:(vol/avgV).toFixed(1)+"×"};if(spread>avgSpread*1.5&&vol>avgV*1.3&&body<.3)return{s:cn[n].close>cn[n].open?"LONG":"SHORT",c:.6,r:`Wide spread (${spread.toFixed(3)}% vs avg ${avgSpread.toFixed(3)}%). Vol ${(vol/avgV).toFixed(1)}×. Small body = indecision → fade.`,sl:cn[n].close>cn[n].open?cl[n]-at[n]:cl[n]+at[n],tp:cn[n].close>cn[n].open?cl[n]+.8*at[n]:cl[n]-.8*at[n],ind};return{s:"HOLD",c:0,r:`Spread ${spread.toFixed(3)}% — normal range.`,ind};}

function sigFlash(cn,cl){const n=cl.length-1;if(n<10)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const roc1=(cl[n]-cl[n-1])/cl[n-1]*100;const roc3=(cl[n]-cl[Math.max(0,n-3)])/cl[Math.max(0,n-3)]*100;const vol=cn[n].volume,avgV=cn.slice(Math.max(0,n-10),n).reduce((a,c)=>a+c.volume,0)/10;const at=atr(cn);const ind={ROC1:roc1.toFixed(2)+"%",ROC3:roc3.toFixed(2)+"%",Vol:(vol/avgV).toFixed(1)+"×"};if(roc1>0.5&&roc3>1&&vol>avgV*2)return{s:"LONG",c:.65,r:`Impulse UP — ROC1 ${roc1.toFixed(2)}%, 3-bar ${roc3.toFixed(1)}%. Vol ${(vol/avgV).toFixed(1)}×. Riding momentum.`,sl:cl[n]-at[n],tp:cl[n]+1.5*at[n],ind};if(roc1<-0.5&&roc3<-1&&vol>avgV*2)return{s:"SHORT",c:.65,r:`Impulse DOWN — ROC1 ${roc1.toFixed(2)}%, vol spike. Riding sell pressure.`,sl:cl[n]+at[n],tp:cl[n]-1.5*at[n],ind};return{s:"HOLD",c:0,r:`No impulse. ROC1 ${roc1.toFixed(2)}%.`,ind};}

function sigSurge(cn,cl){const n=cl.length-1;if(n<15)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const vol=cn[n].volume,avgV=cn.slice(Math.max(0,n-20),n).reduce((a,c)=>a+c.volume,0)/20;const vr=vol/avgV;const delta=cn[n].close-cn[n].open;const body=Math.abs(delta);const range=cn[n].high-cn[n].low||1;const bodyRatio=body/range;const at=atr(cn);const ind={Vol:vr.toFixed(1)+"×",Body:bodyRatio.toFixed(2),Delta:delta>0?"BUY":"SELL"};if(vr>2.5&&bodyRatio>.6&&delta>0)return{s:"LONG",c:.65,r:`BUY FLOW — Vol ${vr.toFixed(1)}× with ${(bodyRatio*100).toFixed(0)}% body ratio. Strong buyers.`,sl:cn[n].low,tp:cl[n]+1.5*at[n],ind};if(vr>2.5&&bodyRatio>.6&&delta<0)return{s:"SHORT",c:.65,r:`SELL FLOW — Vol ${vr.toFixed(1)}× heavy selling. Body ${(bodyRatio*100).toFixed(0)}%.`,sl:cn[n].high,tp:cl[n]-1.5*at[n],ind};return{s:"HOLD",c:0,r:`Vol ${vr.toFixed(1)}×, body ${(bodyRatio*100).toFixed(0)}%. No flow signal.`,ind};}

function sigAbyss(cn,cl,hCn,hCl){const n=cl.length-1;if(n<30)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const rs=rsi(cl,14),at=atr(cn);const hi30=Math.max(...cl.slice(Math.max(0,n-30)));const dd=(cl[n]-hi30)/hi30*100;const vol=cn[n].volume,avgV=cn.slice(Math.max(0,n-20),n).reduce((a,c)=>a+c.volume,0)/20;const vr=vol/avgV;let dRSI=50;if(hCl?.length>14){const dr=rsi(hCl);dRSI=dr[dr.length-1];}const ind={Drawdown:dd.toFixed(1)+"%",RSI_4h:rs[n].toFixed(1),RSI_D:dRSI.toFixed(1),Vol:vr.toFixed(1)+"×"};if(dd<-15&&rs[n]<25&&dRSI<30&&vr>2&&rs[n]>rs[n-1])return{s:"LONG",c:.85,r:`CAPITULATION — ${dd.toFixed(1)}% from 30d high. 4h RSI ${rs[n].toFixed(1)}, Daily ${dRSI.toFixed(1)}. Vol spike ${vr.toFixed(1)}×. DCA entry.`,sl:cl[n]*(1-.2),tp:cl[n]*1.15,ind};if(dd<-10&&rs[n]<30&&dRSI<35&&vr>1.5&&rs[n]>rs[n-1])return{s:"LONG",c:.6,r:`Pre-capitulation — ${dd.toFixed(1)}% drawdown. RSIs low. Watching for deepening.`,sl:cl[n]*(1-.15),tp:cl[n]*1.1,ind};return{s:"HOLD",c:0,r:`Drawdown ${dd.toFixed(1)}%. Need -15%+ with RSI<25 + vol spike. Dormant.`,ind};}

function sigSpecter(cn,cl){const n=cl.length-1;if(n<25)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const rs=rsi(cl,14),ob=obv(cn),e50=ema(cl,50),at=atr(cn);const priceROC=(cl[n]-cl[Math.max(0,n-10)])/cl[Math.max(0,n-10)]*100;const obvROC=(ob[n]-ob[Math.max(0,n-10)])/(Math.abs(ob[Math.max(0,n-10)])||1)*100;const divergence=obvROC-priceROC;const ind={OBV_ROC:obvROC.toFixed(1)+"%",Price_ROC:priceROC.toFixed(1)+"%",RSI:rs[n].toFixed(1),Div:divergence.toFixed(1)};if(divergence>8&&Math.abs(priceROC)<1&&rs[n]>45&&rs[n]<55)return{s:"LONG",c:.7,r:`STEALTH ACCUMULATION — OBV rising ${obvROC.toFixed(1)}% while price flat (${priceROC.toFixed(1)}%). RSI neutral ${rs[n].toFixed(1)}.`,sl:cl[n]-1.5*at[n],tp:cl[n]+2.5*at[n],ind};if(divergence<-8&&Math.abs(priceROC)<1&&rs[n]>45&&rs[n]<55)return{s:"SHORT",c:.7,r:`STEALTH DISTRIBUTION — OBV falling while price flat. Hidden selling.`,sl:cl[n]+1.5*at[n],tp:cl[n]-2.5*at[n],ind};return{s:"HOLD",c:0,r:`Divergence ${divergence.toFixed(1)}. Need ±8 with flat price + neutral RSI.`,ind};}

function sigTrendRider(cn,cl,hCn,hCl){const n=cl.length-1;if(n<30)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const mc=macd(cl),e50=ema(cl,50),at=atr(cn);let dB="neutral";if(hCl?.length>30){const dm=macd(hCl);dB=dm.hist[dm.hist.length-1]>0?"bullish":"bearish";}const ind={MACD:mc.line[n].toFixed(2),Signal:mc.signal[n].toFixed(2),Hist:mc.hist[n].toFixed(2),Daily:dB};if(n>0&&mc.line[n]>mc.signal[n]&&mc.line[n-1]<=mc.signal[n-1]&&mc.hist[n]>0&&cl[n]>e50[n]&&dB!=="bearish")return{s:"LONG",c:dB==="bullish"?.8:.65,r:`MACD bullish cross above signal. Histogram positive. Daily: ${dB}.`,sl:cl[n]-1.5*at[n],tp:cl[n]+2.5*at[n],ind};if(n>0&&mc.line[n]<mc.signal[n]&&mc.line[n-1]>=mc.signal[n-1]&&mc.hist[n]<0&&cl[n]<e50[n]&&dB!=="bullish")return{s:"SHORT",c:dB==="bearish"?.8:.65,r:`MACD bearish cross. Daily: ${dB}.`,sl:cl[n]+1.5*at[n],tp:cl[n]-2.5*at[n],ind};return{s:"HOLD",c:0,r:`MACD ${mc.hist[n]>0?"positive":"negative"}, no cross. Daily: ${dB}.`,ind};}

function sigFlicker(cn,cl){const n=cl.length-1;if(n<20)return{s:"HOLD",c:0,r:"Warming up",ind:{}};const e20=ema(cl,20),at=atr(cn);const spread=cl[n]-e20[n];const spreadPct=spread/e20[n]*100;const spreadHist=[];for(let i=Math.max(0,n-20);i<=n;i++)spreadHist.push(cl[i]-(ema(cl,20)[i]||cl[i]));const avgSpread=spreadHist.reduce((a,b)=>a+b,0)/spreadHist.length;let sumSq=0;spreadHist.forEach(s=>sumSq+=(s-avgSpread)**2);const spreadSD=Math.sqrt(sumSq/spreadHist.length);const zSpread=spreadSD?(spread-avgSpread)/spreadSD:0;const ind={Spread:spreadPct.toFixed(3)+"%",Z_spread:zSpread.toFixed(2)};if(zSpread<-2&&zSpread>-4)return{s:"LONG",c:.65,r:`Spread Z ${zSpread.toFixed(2)} — price ${spreadPct.toFixed(3)}% from EMA20. Convergence expected.`,sl:cl[n]-2*at[n],tp:e20[n],ind};if(zSpread>2&&zSpread<4)return{s:"SHORT",c:.65,r:`Spread Z ${zSpread.toFixed(2)} — overextended above EMA20. Mean reversion.`,sl:cl[n]+2*at[n],tp:e20[n],ind};return{s:"HOLD",c:0,r:`Spread Z ${zSpread.toFixed(2)}. Need ±2.`,ind};}

const SIG={titan:sigTitan,phantom:sigPhantom,reversal:sigReversal,razor:sigRazor,breakout:sigBreakout,fortress:sigFortress,pulse:sigPulse,grokker:sigGrokker,comet:sigComet,blitz:sigBlitz,shield:()=>({s:"HEDGE",c:.5,r:"Auto-hedge active",ind:{}}),sensei:sigSensei,oracle:sigOracle,viper:sigViper,voyager:sigVoyager,momentum:sigMomentum,glider:sigGlider,wraith:sigWraith,needle:sigNeedle,scalper:sigScalper,compass:sigCompass,vertex:sigVertex,flash:sigFlash,surge:sigSurge,abyss:sigAbyss,specter:sigSpecter,trend_rider:sigTrendRider,flicker:sigFlicker};

// ═══ CONDUCTORS ═══
const CD={
  aegis:{n:"Aegis",c:"#4A6FA5",rk:"Conservative",db:-.08,ct:.75,ag:["titan","reversal","comet","shield","fortress","pulse","sensei","glider","oracle"],w:{titan:.15,reversal:.12,comet:.10,shield:.10,fortress:.08,pulse:.06,sensei:.06,glider:.05,oracle:.05}},
  atlas:{n:"Atlas",c:"#1B8A6B",rk:"Balanced",db:-.15,ct:.55,ag:["titan","phantom","reversal","grokker","shield","razor","trend_rider","pulse","abyss","specter"],w:{titan:.18,phantom:.14,reversal:.12,grokker:.10,shield:.10,razor:.08,trend_rider:.07,pulse:.06,abyss:.05,specter:.05}},
  apex_c:{n:"Apex",c:"#E85D26",rk:"Aggressive",db:-.25,ct:.45,ag:["titan","phantom","grokker","breakout","razor","blitz","abyss","viper","momentum","flicker"],w:{titan:.18,phantom:.15,grokker:.13,breakout:.10,razor:.10,blitz:.08,abyss:.07,viper:.06,momentum:.06,flicker:.05}},
  phantom_edge:{n:"Phantom Edge",c:"#9B30FF",rk:"Degen",db:-.35,ct:.35,ag:["titan","phantom","grokker","razor","breakout","blitz","abyss","wraith","needle","flash","surge"],w:{titan:.16,phantom:.14,grokker:.12,razor:.10,breakout:.10,blitz:.08,abyss:.07,wraith:.06,needle:.05,flash:.05,surge:.05}},
};

// ═══ STATE ═══
const START_CAP = 10000;
let candles = {};    // { "4h": { "BTCUSDT": [...] }, ... }
let portfolios = {}; // { aegis: { cap, peak, agents, hist, dd, cb, tc }, ... }
let positions = {};  // { "aegis_titan_BTCUSDT": { entry, size, dir, ot, sl, tp } }
let tradeLog = [];   // last 500 trades
let regime = "ranging";
let tick = 0;
let lastCycleTime = null;
let status = "STARTING";

function initPortfolios() {
  Object.entries(CD).forEach(([id, c]) => {
    const as = {};
    c.ag.forEach(a => { as[a] = { pnl: 0, trades: 0, wins: 0, ls: "HOLD", lr: "", op: 0 }; });
    portfolios[id] = { cap: START_CAP, peak: START_CAP, agents: as, hist: [{ t: Date.now(), v: START_CAP }], dd: 0, cb: false, tc: 0 };
  });
}

// ═══ BINANCE FETCH ═══
async function fetchCandles(initial = false) {
  const tfs = new Set();
  Object.values(AG).forEach(a => { tfs.add(a.tf); if (a.htf) tfs.add(a.htf); });
  tfs.add("4h");
  const limit = initial ? 100 : 3;

  for (const tf of tfs) {
    if (!candles[tf]) candles[tf] = {};
    for (const pair of PAIRS) {
      try {
        const res = await fetch(`https://api.binance.com/api/v3/klines?symbol=${pair}&interval=${tf}&limit=${limit}`);
        const raw = await res.json();
        if (!raw?.length) continue;
        const data = raw.map(k => ({ time: k[0], open: +k[1], high: +k[2], low: +k[3], close: +k[4], volume: +k[5] }));
        if (initial) {
          candles[tf][pair] = data;
        } else {
          if (!candles[tf][pair]) candles[tf][pair] = [];
          const ex = candles[tf][pair];
          data.forEach(c => { const idx = ex.findIndex(e => e.time === c.time); if (idx >= 0) ex[idx] = c; else ex.push(c); });
          if (ex.length > 150) ex.splice(0, ex.length - 150);
        }
      } catch (e) { /* skip */ }
      await new Promise(r => setTimeout(r, 40));
    }
  }
}

// ═══ REGIME DETECTION (4h BTC) ═══
function detectRegime() {
  const btc = candles?.["4h"]?.BTCUSDT;
  if (!btc || btc.length < 20) return "ranging";
  const cl = btc.map(c => c.close); const n = cl.length - 1;
  const e8 = ema(cl, 8), e21 = ema(cl, 21), rs = rsi(cl);
  const pc = (cl[n] - cl[Math.max(0, n - 12)]) / cl[Math.max(0, n - 12)];
  if (pc < -.08) return "crash";
  if (e8[n] > e21[n] && rs[n] > 50) return "bull";
  if (e8[n] < e21[n] && rs[n] < 50) return "bear";
  return "ranging";
}

// ═══ SIMULATION CYCLE ═══
function runCycle() {
  regime = detectRegime();
  const em = regime === "crash" ? .2 : regime === "bear" ? .6 : regime === "bull" ? 1.2 : 1;
  const newTrades = [];

  Object.entries(CD).forEach(([cId, cond]) => {
    if (!portfolios[cId]) return;
    const port = portfolios[cId];
    const ags = port.agents;
    if (port.cb) return;

    cond.ag.forEach(aId => {
      if (!ags[aId]) return;
      const agent = AG[aId]; const sigFn = SIG[aId]; if (!sigFn) return;
      const agTF = agent.tf; const agHTF = agent.htf;

      const ps = PAIRS.map(pair => {
        const cn = candles[agTF]?.[pair]; if (!cn?.length || cn.length < 20) return { pair, sc: 0 };
        const cl = cn.map(c => c.close);
        const hCn = agHTF ? candles[agHTF]?.[pair] : null;
        const hCl = hCn?.map(c => c.close);
        const sig = aId === "comet" ? sigFn(cn, cl, hCn, hCl, tick) : sigFn(cn, cl, hCn, hCl);
        return { pair, sc: sig.c, sig, cn, cl };
      }).sort((a, b) => b.sc - a.sc);

      const best = ps[0]; if (!best?.sig) return;
      const pk = `${cId}_${aId}_${best.pair}`; const ex = positions[pk];
      const cp = best.cl[best.cl.length - 1]; const wt = cond.w[aId] || .1;
      ags[aId].ls = best.sig.s; ags[aId].lr = best.sig.r; ags[aId].lp = PL[best.pair];
      if (aId === "shield") return;

      // Close existing positions
      if (ex) {
        const pp = ex.dir === "long" ? (cp - ex.entry) / ex.entry : (ex.entry - cp) / ex.entry;
        let sc = false, cr = "";
        if (pp < -.025) { sc = true; cr = `Stop loss on ${agTF}. ${(pp * 100).toFixed(2)}%.`; }
        if (pp > .05) { sc = true; cr = `Take profit on ${agTF}. +${(pp * 100).toFixed(2)}%.`; }
        if (best.sig.s === "HOLD" && pp > .02) { sc = true; cr = `Signal faded, locking +${(pp * 100).toFixed(2)}%.`; }
        if ((ex.dir === "long" && best.sig.s === "SHORT") || (ex.dir === "short" && best.sig.s === "LONG")) { sc = true; cr = `Signal reversed on ${agTF}.`; }
        if (sc) {
          const rp = pp * ex.size; port.cap += rp; ags[aId].pnl += rp; ags[aId].trades++; if (rp > 0) ags[aId].wins++; ags[aId].op--;
          delete positions[pk];
          const trade = { t: Date.now(), cId, aId, pair: best.pair, act: "CLOSE", dir: ex.dir, pnl: rp, pp, reason: cr, price: cp, entry: ex.entry, size: ex.size, dur: Date.now() - ex.ot, ind: best.sig.ind, tf: agTF, htf: agHTF, agentName: agent.n };
          newTrades.push(trade);
        }
        return;
      }

      // Open new positions
      if (best.sig.s === "HOLD" || best.sig.s === "HEDGE") return;
      if (best.sig.c < cond.ct) return;
      const ap = Object.keys(positions).filter(k => k.startsWith(`${cId}_${aId}`)).length; if (ap >= 2) return;
      const dir = best.sig.s === "LONG" ? "long" : "short"; const sz = port.cap * wt * em; if (sz < 10) return;
      positions[pk] = { entry: cp, size: sz, dir, ot: Date.now(), sl: best.sig.sl, tp: best.sig.tp };
      ags[aId].op = (ags[aId].op || 0) + 1; port.tc = (port.tc || 0) + 1;
      const trade = { t: Date.now(), cId, aId, pair: best.pair, act: "OPEN", dir, size: sz, reason: best.sig.r, price: cp, conf: best.sig.c, sl: best.sig.sl, tp: best.sig.tp, ind: best.sig.ind, strat: agent.s, tf: agTF, htf: agHTF, hold: agTF === "1d" || agTF === "1w" ? "weeks" : agTF === "4h" ? "days" : "hours", agentName: agent.n };
      newTrades.push(trade);
    });

    // Update portfolio value
    let up = 0;
    Object.entries(positions).forEach(([k, p]) => {
      if (!k.startsWith(cId)) return;
      const pts = k.split("_"); const pair = pts[2]; const agId = pts[1];
      const agTF = AG[agId]?.tf || "4h";
      const cp2 = candles[agTF]?.[pair]?.[candles[agTF][pair].length - 1]?.close;
      if (!cp2) return;
      up += p.dir === "long" ? (cp2 - p.entry) / p.entry * p.size : (p.entry - cp2) / p.entry * p.size;
    });
    const tv = port.cap + up;
    port.peak = Math.max(port.peak, tv);
    port.dd = (tv - port.peak) / port.peak;
    port.cb = port.dd <= cond.db;
    port.hist = [...port.hist.slice(-200), { t: Date.now(), v: tv }];
  });

  if (newTrades.length) {
    tradeLog = [...newTrades, ...tradeLog].slice(0, 500);
  }
  tick++;
  lastCycleTime = new Date().toISOString();
}

// ═══ PERSISTENCE (Supabase) ═══
async function saveState() {
  if (!supabase) return;
  try {
    const state = { portfolios, positions, regime, tick, lastCycleTime, tradeLog: tradeLog.slice(0, 100) };
    await supabase.from('simulation_state').upsert({ id: 'main', data: state, updated_at: new Date().toISOString() });
    console.log(`[${new Date().toISOString()}] State saved. Tick ${tick}, regime: ${regime}`);
  } catch (e) { console.error('Save error:', e.message); }
}

async function loadState() {
  if (!supabase) return false;
  try {
    const { data } = await supabase.from('simulation_state').select('data').eq('id', 'main').single();
    if (data?.data) {
      portfolios = data.data.portfolios || {};
      positions = data.data.positions || {};
      regime = data.data.regime || "ranging";
      tick = data.data.tick || 0;
      tradeLog = data.data.tradeLog || [];
      console.log(`Loaded state: tick ${tick}, regime: ${regime}, ${tradeLog.length} trades`);
      return true;
    }
  } catch (e) { console.log('No existing state, starting fresh'); }
  return false;
}

async function saveTrade(trade) {
  if (!supabase) return;
  try {
    await supabase.from('trades').insert({
      conductor: trade.cId, agent: trade.aId, agent_name: trade.agentName,
      pair: trade.pair, action: trade.act, direction: trade.dir,
      price: trade.price, size: trade.size, pnl: trade.pnl,
      reason: trade.reason, timeframe: trade.tf, htf: trade.htf,
      confidence: trade.conf, stop_loss: trade.sl, take_profit: trade.tp,
      indicators: trade.ind, created_at: new Date(trade.t).toISOString()
    });
  } catch (e) { /* skip */ }
}

// ═══ MAIN LOOP ═══
async function cycle() {
  try {
    await fetchCandles(tick === 0);
    runCycle();
    await saveState();
    const prices = {};
    PAIRS.forEach(p => { const d = candles["4h"]?.[p]; if (d?.length) prices[p] = d[d.length - 1].close; });
    console.log(`[Tick ${tick}] Regime: ${regime} | BTC: $${prices.BTCUSDT?.toFixed(0)} | Positions: ${Object.keys(positions).length} | Trades today: ${tradeLog.filter(t => Date.now() - t.t < 86400000).length}`);
  } catch (e) {
    console.error('Cycle error:', e.message);
  }
}

// ═══ EXPRESS API ═══
const app = express();
app.use(cors());
app.use(express.json());

// Health check
app.get('/', (req, res) => res.json({ status, tick, regime, lastCycleTime, uptime: process.uptime() }));

// Full state for dashboard
app.get('/api/state', (req, res) => {
  const prices = {};
  PAIRS.forEach(p => { const d = candles["4h"]?.[p]; if (d?.length) prices[p] = d[d.length - 1].close; });
  res.json({
    portfolios, positions, regime, tick, lastCycleTime, status,
    prices, agents: AG, conductors: CD, tradeLog: tradeLog.slice(0, 100)
  });
});

// Trade log with pagination
app.get('/api/trades', (req, res) => {
  const conductor = req.query.conductor;
  const limit = Math.min(parseInt(req.query.limit) || 50, 200);
  const offset = parseInt(req.query.offset) || 0;
  let trades = tradeLog;
  if (conductor) trades = trades.filter(t => t.cId === conductor);
  res.json({ trades: trades.slice(offset, offset + limit), total: trades.length });
});

// Candle data for charts
app.get('/api/candles/:tf/:pair', (req, res) => {
  const data = candles[req.params.tf]?.[req.params.pair];
  if (!data) return res.status(404).json({ error: 'Not found' });
  res.json(data.slice(-100));
});

// ═══ START ═══
async function start() {
  console.log('═══ Agent League Backend Starting ═══');
  console.log(`Supabase: ${supabase ? 'Connected' : 'Not configured (running in-memory only)'}`);

  // Try to load existing state
  const loaded = await loadState();
  if (!loaded) {
    initPortfolios();
    console.log('Fresh start — initializing portfolios');
  }

  // Initial data fetch
  status = "LOADING";
  console.log('Fetching initial candle data (1h, 4h, 1d, 1w × 8 pairs)...');
  await fetchCandles(true);
  console.log('Initial data loaded');

  // Run first cycle
  runCycle();
  await saveState();
  status = "LIVE";
  console.log(`═══ LIVE — Tick ${tick}, Regime: ${regime} ═══`);

  // Schedule: run every 60 seconds
  setInterval(cycle, 60000);

  // Start API server
  app.listen(PORT, () => {
    console.log(`API server running on port ${PORT}`);
    console.log(`Endpoints: GET / | /api/state | /api/trades | /api/candles/:tf/:pair`);
  });
}

start().catch(e => { console.error('Fatal:', e); process.exit(1); });
