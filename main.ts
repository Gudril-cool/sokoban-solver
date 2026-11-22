// Push-optimal Sokoban: hallway cut, per-room push A* (assignment heuristic), stitch.
import {mkdirSync, readdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output',LU='udlr',UU='UDLR',X=1<<28;
const PS=t=>{const r=t.split('\n').filter(e=>e.length),h=r.length,w=Math.max(...r.map(e=>e.length)),z=w*h,a=new Uint8Array(z).fill(1),g=[],b=[];let p=-1;
r.forEach((e,y)=>{for(let x=0;x<e.length;x++){const c=e[x],i=y*w+x;if(c=='#')continue;a[i]=0;if('.*+'.includes(c))g.push(i);if('$*'.includes(c))b.push(i);if('@+'.includes(c))p=i}});
for(let y=0;y<h;y++)for(let x=0;x<w;x++)if(!x||!y||x==w-1||y==h-1)a[y*w+x]=1;
return{w,z,a,g,b,p,D:[-w,w,-1,1],q:new Int32Array(z)};};
const PD=(L,o,G)=>{const{z,D,q}=L,d=new Int32Array(z*G.length).fill(X);
G.forEach((g,gi)=>{const b0=gi*z;let hd=0,tl=0;q[tl++]=g;d[b0+g]=0;
while(hd<tl){const t=q[hd++],v=d[b0+t];
for(let e=0;e<4;e++){const dd=D[e],b=t-dd,s=t-2*dd;if(b<0||b>=z||s<0||s>=z||!o[b]||!o[s]||d[b0+b]!==X)continue;d[b0+b]=v+1;q[tl++]=b}}});
return d;};
const PM=n=>{const o=[],c=[],u=new Array(n).fill(false);const f=()=>{if(c.length==n){o.push(c.slice());return}for(let i=0;i<n;i++)if(!u[i]){u[i]=true;c.push(i);f();c.pop();u[i]=false}};f();return o};
const WK=(L,o,c,F,T)=>{if(F==T)return'';
const{z,D,q}=L,v=new Int32Array(z).fill(-1);let hd=0,tl=0;q[tl++]=F;v[F]=F*4;
while(hd<tl){const p=q[hd++];if(p==T)break;for(let e=0;e<4;e++){const n=p+D[e];if(n<0||n>=z||!o[n]||c[n]||v[n]!==-1)continue;v[n]=p*4+e;q[tl++]=n}}
if(v[T]===-1)return null;let s='';for(let p=T;p!==F;p=v[p]>>2)s=LU[v[p]&3]+s;return s;};
const SP=(L,o,B,G,P0)=>{const{z,D,q}=L,k=B.length,d=PD(L,o,G),pm=PM(k);
const H=b=>{let s=X;for(const p of pm){let v=0;for(let i=0;i<k;i++){const e=d[p[i]*z+b[i]];if(e>=X){v=X;break}v+=e}if(v<s)s=v}return s};
const h0=H(B);if(h0>=X)return null;
const C=new Int32Array(z),N=new Int32Array(z),c=new Uint8Array(z);let tC=0,tN=0;
const FL=(s2,m,F)=>{let n=0,l=F;q[n++]=F;s2[F]=m;
while(n){const p=q[--n];if(p<l)l=p;for(let e=0;e<4;e++){const u=p+D[e];if(u<0||u>=z||!o[u]||c[u]||s2[u]===m)continue;s2[u]=m;q[n++]=u}}return l};
const KY=(b,l)=>{let y=l;for(const e of b)y=y*z+e;return y};
const NB=[B.slice()],NP=[P0],NG=[0],PA=[-1],bs=new Map();
for(const e of B)c[e]=1;bs.set(KY(B,FL(N,++tN,P0)),0);for(const e of B)c[e]=0;
const Q=[];let bf=h0;
const PU=(f,n)=>{(Q[f]??=[]).push(n);if(f<bf)bf=f};
PU(bf,0);
let fd=-1;
while(fd<0){while(bf<Q.length&&(!Q[bf]||!Q[bf].length))bf++;if(bf>=Q.length)break;
const s=Q[bf].pop(),b=NB[s],g=NG[s];
if(b.every(e=>G.includes(e))){fd=s;break}
for(const e of b)c[e]=1;FL(C,++tC,NP[s]);
for(let bi=0;bi<k;bi++){const e=b[bi];
for(let j=0;j<4;j++){const dd=D[j],sd=e-dd,t=e+dd;
if(sd<0||sd>=z||t<0||t>=z||C[sd]!==tC||!o[t]||c[t])continue;
c[e]=0;c[t]=1;const nx=b.slice();nx[bi]=t;nx.sort((u,v)=>u-v);const ky=KY(nx,FL(N,++tN,e));c[t]=0;c[e]=1;
const ng=g+1,sg=bs.get(ky);if(sg!==undefined&&sg<=ng)continue;
if(NB.length>=1e6){for(const u of b)c[u]=0;return null}
bs.set(ky,ng);const id=NB.length;NB.push(nx);NP.push(e);NG.push(ng);PA.push(s);
const hh=H(nx);if(hh<X)PU(ng+hh,id)}}
for(const e of b)c[e]=0}
if(fd<0)return null;
const pt=[];for(let s=fd;s>0;s=PA[s])pt.push(s);pt.reverse();
let mv='',pl=P0,b=B;
for(const s of pt){const nx=NB[s],F=b.find(e=>!nx.includes(e)),T=nx.find(e=>!b.includes(e)),dd=T-F;
for(const e of b)c[e]=1;const wk=WK(L,o,c,pl,F-dd);for(const e of b)c[e]=0;
if(wk===null)return null;mv+=wk+UU[D.indexOf(dd)];pl=F;b=nx}
return mv;};
const RM=L=>{const{w,z,a,g,b,p,D,q}=L,o=new Uint8Array(z);
for(let s=0;s<z;s++)o[s]=a[s]?0:1;
L.ao=o;
const d=PD(L,o,g),lv=new Uint8Array(z);
for(let s=0;s<z;s++)for(let e=0;e<g.length;e++)if(d[e*z+s]<X){lv[s]=1;break}
const rw=Math.floor(p/w),ct=new Uint8Array(z);
for(let x=0;x<w;x++){const i=rw*w+x;if(!a[i]&&!lv[i])ct[i]=1}
if(b.some(e=>ct[e]===1))return null;
const pt=new Int32Array(z).fill(-1),rs=[];
for(let s=0;s<z;s++){if(a[s]||ct[s]||pt[s]>=0)continue;
const id=rs.length,sq=[];let tn=0;pt[s]=id;q[tn++]=s;
while(tn){const u=q[--tn];sq.push(u);for(let e=0;e<4;e++){const n=u+D[e];if(n<0||n>=z||a[n]||ct[n]||pt[n]>=0)continue;pt[n]=id;q[tn++]=n}}
rs.push({sq,b:[],g:[],en:-1})}
for(const e of b){if(pt[e]<0)return null;rs[pt[e]].b.push(e)}
for(const e of g){if(pt[e]<0)return null;rs[pt[e]].g.push(e)}
const kp=[];
for(const r of rs){if(!r.b.length)continue;if(r.b.length!==r.g.length)return null;r.sq.sort((u,v)=>u-v);
for(const s of r.sq){for(let e=0;e<4;e++){const u=s+D[e];if(u>=0&&u<z&&Math.floor(u/w)===rw&&!a[u]){r.en=u;break}}if(r.en>=0)break}
if(r.en<0)return null;kp.push(r)}
return kp;};
const BR=(L,rs)=>{const{z}=L,set=new Set(L.b),c=new Uint8Array(z);let pl=L.p,mv='';
for(const r of rs){for(const e of set)c[e]=1;const wk=WK(L,L.ao,c,pl,r.en);for(const e of set)c[e]=0;
if(wk===null)return null;mv+=wk;pl=r.en;
const o=new Uint8Array(z);for(const s of r.sq)o[s]=1;o[r.en]=1;
const sl=SP(L,o,r.b,r.g,r.en);
if(sl===null)return null;mv+=sl;
let p=pl;for(const ch of sl){const e=LU.indexOf(ch.toLowerCase());if(e<0)continue;const u=p+L.D[e];if(set.has(u)){set.delete(u);set.add(u+L.D[e])}p=u}pl=p;
if(!r.g.every(e=>set.has(e)))return null}
return L.g.every(e=>set.has(e))?mv:null;};
for(const id of readdirSync(I).sort()){const L=PS(readFileSync(join(I,id,'level.txt'),'utf8'));let mv='';
if(L.b.length&&L.p>=0){const rs=RM(L);if(rs&&rs.length){const m=BR(L,rs);if(m!==null)mv=m}}
mkdirSync(join(O,id),{recursive:true});writeFileSync(join(O,id,'solution.txt'),mv+'\n')}
