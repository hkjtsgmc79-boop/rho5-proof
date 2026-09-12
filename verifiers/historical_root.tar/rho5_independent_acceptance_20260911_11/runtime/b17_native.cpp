// B17 canonical interval and C/H arithmetic. No X objective or B18 contacts.
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/json_parser.hpp>
#include <algorithm>
#include <array>
#include <cmath>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>
#include "b17_native_data.hpp"

using R = boost::multiprecision::cpp_rational;
using Big = boost::multiprecision::cpp_int;
using J = boost::property_tree::ptree;
static Big integer(const std::string& s) {
    if (s.empty()) throw std::runtime_error("empty integer");
    size_t i=(s[0]=='-' || s[0]=='+')?1:0;
    if (i==s.size()) throw std::runtime_error("invalid integer");
    Big value=0;
    for (;i<s.size();++i) { if(s[i]<'0'||s[i]>'9')throw std::runtime_error("invalid integer"); value*=10;value+=s[i]-'0'; }
    return s[0]=='-'?-value:value;
}
static R rat(const std::string& s) {
    auto pos=s.find('/');
    if(pos==std::string::npos)return R(integer(s));
    Big d=integer(s.substr(pos+1));if(d==0)throw std::runtime_error("zero denominator");
    return R(integer(s.substr(0,pos)))/R(d);
}
static R mn(const R&a,const R&b){return a<b?a:b;}
static R mx(const R&a,const R&b){return a>b?a:b;}
static R ab(const R&a){return a<0?-a:a;}
static std::string str(const R& r) {
    auto n=numerator(r).convert_to<std::string>(), d=denominator(r).convert_to<std::string>();
    return d=="1"?n:n+"/"+d;
}
static J parse(const std::string& s){std::istringstream in(s);J j;boost::property_tree::read_json(in,j);return j;}
static std::string encode(const J& j){std::ostringstream out;boost::property_tree::write_json(out,j,false);return out.str();}
static J scalar(const std::string& s){J j;j.put_value(s);return j;}
static void push(J& a,const J& v){a.push_back({"",v});}
struct I {
    R lo,hi;
    I():lo(0),hi(0){} I(long v):lo(v),hi(v){} I(const R&v):lo(v),hi(v){}
    I(const R&l,const R&h):lo(l),hi(h){if(lo>hi)throw std::runtime_error("reversed interval");}
};
static I operator+(const I&a,const I&b){return I(a.lo+b.lo,a.hi+b.hi);}
static I operator-(const I&a){return I(-a.hi,-a.lo);}
static I operator-(const I&a,const I&b){return a+-b;}
static I operator*(const I&a,const I&b){std::array<R,4>v={R(a.lo*b.lo),R(a.lo*b.hi),R(a.hi*b.lo),R(a.hi*b.hi)};return I(*std::min_element(v.begin(),v.end()),*std::max_element(v.begin(),v.end()));}
static I operator/(const I&a,const I&b){if(b.lo<=0&&b.hi>=0)throw std::runtime_error("interval divisor contains zero");return a*I(R(1)/b.hi,R(1)/b.lo);}
static I imin(const I&a,const I&b){return I(mn(a.lo,b.lo),mn(a.hi,b.hi));}
static I imax(const I&a,const I&b){return I(mx(a.lo,b.lo),mx(a.hi,b.hi));}
static I imin(const std::vector<I>& a){if(a.empty())throw std::runtime_error("empty minimum");I z=a[0];for(size_t i=1;i<a.size();++i)z=imin(z,a[i]);return z;}
static I imax(const std::vector<I>& a){if(a.empty())throw std::runtime_error("empty maximum");I z=a[0];for(size_t i=1;i<a.size();++i)z=imax(z,a[i]);return z;}
static bool intersect(const I&a,const I&b,I&out){R l=mx(a.lo,b.lo),h=mn(a.hi,b.hi);if(l>h)return false;out=I(l,h);return true;}
static bool overlap(const I&a,const I&b){return a.lo<=b.hi&&b.lo<=a.hi;}
static J interval_json(const I&v){J j;push(j,scalar(str(v.lo)));push(j,scalar(str(v.hi)));return j;}
static J intervals_json(const std::vector<I>&v){J j;for(auto&a:v)push(j,interval_json(a));return j;}
static std::vector<I> intervals(const J&j){std::vector<I> v;for(auto&entry:j){auto&a=entry.second;if(a.size()!=2)throw std::runtime_error("interval needs two ends");auto it=a.begin();R lo=rat(it->second.data());++it;v.emplace_back(lo,rat(it->second.data()));}return v;}

struct Row {std::map<int,R> co;R rhs=0;};
struct Oracle {std::string status="OPEN",reason,port;bool charts=false;int contraction_rounds=0;R ub=0,budget=0,gain=0;std::vector<I>aux,gap;};
struct Engine {
    J data;R gamma,alpha;std::vector<I>root;std::vector<std::vector<R>>centers;
    std::vector<Row>base;std::vector<std::pair<int,int>>pairs;int nv=24,n=62,fi=23;
    Engine() {
        data=parse(B17_DATA);gamma=rat(data.get<std::string>("gamma"));alpha=rat(data.get<std::string>("alpha_lower"));root=intervals(data.get_child("root"));
        int index=0;for(auto&x:data.get_child("coordinates")){if(x.second.data()=="F")fi=index;++index;}nv=index;
        std::set<std::pair<int,int>> ps;
        for(auto&row:data.get_child("rows"))for(auto&term:row.second){auto&m=term.second.get_child("monomial");if(m.size()==2){auto it=m.begin();int a=it->second.get_value<int>();++it;int b=it->second.get_value<int>();ps.emplace(a,b);}}
        pairs.assign(ps.begin(),ps.end());n=nv+pairs.size();
        if(root.size()!=17||nv!=24||fi!=23||pairs.size()!=38||data.get_child("rows").size()!=106)throw std::runtime_error("wrong B17 data shape");
        for(auto&rr:data.get_child("rows")){
            Row row;
            for(auto&tt:rr.second){auto&t=tt.second;R a=rat(t.get<std::string>("coefficient"));auto&m=t.get_child("monomial");
                if(m.empty())row.rhs+=a;
                else {auto it=m.begin();int i=it->second.get_value<int>();if(m.size()==2){++it;int j=it->second.get_value<int>();auto p=std::lower_bound(pairs.begin(),pairs.end(),std::make_pair(i,j));i=nv+std::distance(pairs.begin(),p);}else if(m.size()!=1)throw std::runtime_error("unexpected degree");row.co[i]-=a;}}
            base.push_back(row);
        }
        for(auto&c:data.get_child("centers")){std::vector<R>v;for(auto&x:c.second)v.push_back(rat(x.second.data()));if(v.size()!=24)throw std::runtime_error("wrong flow dictionary");centers.push_back(v);}
        if(centers.size()!=4)throw std::runtime_error("wrong flow centers");
    }
    bool beta_image(const std::vector<I>&v,const std::vector<I>&q,I&beta){
        std::vector<I>lows={I(0)},ups={I(1)};bool complete=true;
        for(int j=0;j<3;++j){I vi=v[j],qi=q[j];
            if(vi.lo>0){lows.push_back((I(-1)-qi)/vi);ups.push_back((I(1)-qi)/vi);}
            else if(vi.hi<0){lows.push_back((I(1)-qi)/vi);ups.push_back((I(-1)-qi)/vi);}
            else if(vi.lo==0&&vi.hi==0){if(!overlap(qi,I(-1,1)))return false;}
            else{complete=false;if(!overlap(qi+I(0,1)*vi,I(-1,1)))return false;}}
        I blo=imax(lows),bhi=imin(ups);if(blo.lo>bhi.hi||bhi.hi<0)return false;
        beta=I(complete?mx(R(0),bhi.lo):R(0),mn(R(1),bhi.hi));return true;
    }
    bool prefix(const std::vector<I>&u,const std::vector<I>&x,const I&beta,I&p,I&e,bool&complete){
        std::vector<std::pair<I,I>>rows={{I(1),beta}};complete=beta.lo>0;
        std::vector<I>upper={I(1)+beta};
        for(int j=0;j<3;++j){I xi=x[j],ui=u[j],a,b;if(xi.lo==0&&xi.hi==0)continue;
            if(xi.lo>0){a=xi;b=ui;}else if(xi.hi<0){a=-xi;b=-ui;}else{complete=false;continue;}
            rows.emplace_back(a,b);upper.push_back((I(1)+imax(I(0),b))/a);
            if(!(b.lo>0||b.hi<0||(b.lo==0&&b.hi==0)))complete=false;
        }
        std::vector<I>caps;for(auto&row:rows)if(row.second.lo>=0)caps.push_back((I(1)+row.second)/row.first);
        for(auto&ri:rows)if(ri.second.lo>0)for(auto&rj:rows)if(rj.second.hi<0)
            caps.push_back((ri.second-rj.second)/(rj.first*ri.second-ri.first*rj.second));
        upper.insert(upper.end(),caps.begin(),caps.end());R pu=2;for(auto&z:upper)pu=mn(pu,z.hi);if(pu<1)return false;
        if(complete){if(!intersect(imin(caps),I(1,2),p))return false;std::vector<I>es={I(0)};
            for(auto&row:rows)if(row.second.lo>0)es.push_back((row.first*p-I(1))/row.second);
            if(!intersect(imax(es),I(0,1),e))return false;
        }else{p=I(1,pu);e=I(0,1);}return true;
    }
    Oracle oracle(const std::vector<I>&b,bool ports=true){
        if(b.size()!=17)throw std::runtime_error("17 frame intervals required");
        for(int i=0;i<17;++i)if(b[i].lo<root[i].lo||b[i].hi>root[i].hi)throw std::runtime_error("outside frozen root");
        Oracle out;auto empty=[&](const std::string&reason){Oracle z;z.status="EMPTY";z.reason=reason;return z;};
        I k=b[0],A=b[1],B=b[2],c=b[3],d=b[4],beta,p,e;
        std::vector<I>u(b.begin()+5,b.begin()+8),x(b.begin()+8,b.begin()+11),v(b.begin()+11,b.begin()+14),q(b.begin()+14,b.end());
        if(k.lo<=0)throw std::runtime_error("nonpositive k lower bound");
        for(int i=5;i<14;++i)if(!overlap(b[i],I(-1,1)))return empty("receiver_box");
        if(!beta_image(v,q,beta))return empty("beta_interval");
        if(!prefix(u,x,beta,p,e,out.charts))return empty("prefix_capacity");
        if(!intersect(p,I(gamma/4,mn(R(2),R(4)/k.lo)),p))return empty("prefix_low_order_bound");
        for(auto&qi:q)if((p-qi).hi<0||(p+qi).hi<0)return empty("q_stage");
        std::vector<std::tuple<int,int,I>>fixed={{0,0,k},{0,1,A},{0,2,B},{1,0,c*k},{2,0,d*k}};
        for(auto&cell:fixed){int i=std::get<0>(cell),j=std::get<1>(cell);I z=std::get<2>(cell);std::string ij=std::to_string(i)+std::to_string(j);
            if((k-z).hi<0||(k+z).hi<0)return empty("D"+ij);
            I ss=z+x[i]*q[j],oo=ss+u[i]*v[j];if((p-ss).hi<0||(p+ss).hi<0)return empty("S"+ij);
            if((I(1)-oo).hi<0||(I(1)+oo).hi<0)return empty("O"+ij);
        }
        I lo[3][3],up[3][3];for(int i=1;i<3;++i)for(int j=1;j<3;++j){I xx=x[i]*q[j],yy=u[i]*v[j];
            lo[i][j]=imax(std::vector<I>{-k,-p-xx,I(-1)-xx-yy});up[i][j]=imin(std::vector<I>{k,p-xx,I(1)-xx-yy});
            if(lo[i][j].lo>up[i][j].hi)return empty("cell_"+std::to_string(i)+std::to_string(j));}
        I ca=c*A,cb=c*B,da=d*A,db=d*B;
        I rl=imax(std::vector<I>{I(0),lo[1][1]-ca,db-up[2][2]}),r=imin(up[1][1]-ca,db-lo[2][2]);
        I sl=imax(I(0),lo[1][2]-cb),su=up[1][2]-cb,tl=imax(I(0),lo[2][1]-da),tu=up[2][1]-da;
        if(!intersect(r,I(gamma/2,mn(R(4),R(2)*k.hi)),r)||r.hi<rl.lo)return empty("r_capacity");
        r=I(mx(r.lo,rl.lo),r.hi);I s,t;
        R slb=mx(R(0),sl.lo),tlb=mx(R(0),tl.lo);
        if(slb>r.hi||tlb>r.hi||!intersect(imin(r,su),I(slb,r.hi),s)||!intersect(imin(r,tu),I(tlb,r.hi),t))return empty("arm_capacity");
        I sig,tau;if(!intersect(imax(I(0),r-su),I(R(0),r.hi),sig)||!intersect(imax(I(0),r-tu),I(R(0),r.hi),tau))return empty("gap_capacity");
        out.ub=mn(mn(R(r.hi+s.hi*t.hi/r.hi),R(9)*k.hi/4),R(4)*p.hi);
        if(out.ub<gamma)return empty("height_below_trigger");
        out.gap={k,r,-r,A,B,c,d,p,e,beta};out.aux={k,r,s,t,A,B,c,d,p,e,beta};
        for(auto*vec:{&u,&x,&v,&q}){out.gap.insert(out.gap.end(),vec->begin(),vec->end());out.aux.insert(out.aux.end(),vec->begin(),vec->end());}
        out.gap.push_back(sig);out.gap.push_back(tau);out.aux.emplace_back(gamma,out.ub);
        if(out.ub<=alpha){out.status="SAFE";out.port="height";return out;}
        if(ports)for(size_t j=0;j<centers.size();++j){R dist=0;for(int i=0;i<24;++i)dist=mx(dist,mx(ab(R(out.gap[i].lo-centers[j][i])),ab(R(out.gap[i].hi-centers[j][i]))));
            R budget=dist+3*(sig.hi+tau.hi);if(budget<R(1)/1250){out.status="SAFE";out.port="canonical_flow_"+std::to_string(j);out.budget=budget;out.gain=(sig.lo+tau.lo)/10;return out;}}
        return out;
    }
    Oracle high_value(Oracle out,bool ports=true){
        if(out.status=="EMPTY")return out;
        auto empty=[](const std::string&reason){Oracle z;z.status="EMPTY";z.reason=reason;return z;};
        auto &b=out.aux;
        auto cut=[&](int i,const R&lo,const R&hi){
            R l=mx(b[i].lo,lo),h=mn(b[i].hi,hi);
            if(l>h)throw std::string("high_value_coordinate_")+std::to_string(i);
            b[i]=I(l,h);
        };
        try{
            for(int iteration=0;iteration<8;++iteration){
                auto previous=b;
                I r=b[1],s=b[2],t=b[3],p=b[8],e=b[9],beta=b[10],F=b[23];
                cut(8,b[8].lo,R(1)+e.hi*beta.hi);
                R positive=b[8].lo-1;
                if(positive>0){
                    if(beta.hi<=0||e.hi<=0)throw std::string("high_value_positive_head");
                    cut(9,positive/beta.hi,b[9].hi);cut(10,positive/e.hi,b[10].hi);
                }
                cut(2,F.lo-r.hi,r.hi);cut(3,F.lo-r.hi,r.hi);
                cut(1,mx(mx(mx(b[2].lo,b[3].lo),mx(R(F.lo-b[2].hi),R(F.lo-b[3].hi))),R(F.lo/2)),F.hi);
                r=b[1];s=b[2];t=b[3];F=b[23];
                R product_lo=mx(R(0),mn(R(r.lo*(F.lo-r.lo)),R(r.hi*(F.lo-r.hi))));
                R vertex=F.hi/2;
                R product_hi=(r.lo<=vertex&&vertex<=r.hi)?R(F.hi*F.hi/4):mx(R(r.lo*(F.hi-r.lo)),R(r.hi*(F.hi-r.hi)));
                if(product_hi<0)throw std::string("high_value_product_upper");
                if(product_lo>0){
                    if(t.hi<=0||s.hi<=0)throw std::string("high_value_positive_product");
                    cut(2,product_lo/t.hi,b[2].hi);cut(3,product_lo/s.hi,b[3].hi);
                }
                if(b[3].lo>0)cut(2,b[2].lo,product_hi/b[3].lo);
                if(b[2].lo>0)cut(3,b[3].lo,product_hi/b[2].lo);
                r=b[1];s=b[2];t=b[3];p=b[8];
                cut(23,b[23].lo,mn(mn(R(r.hi+s.hi),R(r.hi+t.hi)),mn(R(r.hi+s.hi*t.hi/r.hi),R(4*p.hi))));
                out.contraction_rounds=iteration+1;
                bool same=true;for(size_t i=0;i<b.size();++i)if(b[i].lo!=previous[i].lo||b[i].hi!=previous[i].hi){same=false;break;}
                if(same)break;
            }
        }catch(const std::string&reason){return empty(reason);}
        std::vector<I>gap={b[0],b[1],-b[1]};gap.insert(gap.end(),b.begin()+4,b.begin()+23);
        for(int axis=2;axis<=3;++axis){
            I z;if(!intersect(b[1]-b[axis],I(R(0),b[1].hi),z)||!intersect(z,out.gap[20+axis],z))return empty("high_value_gap_image");
            gap.push_back(z);
        }
        out.gap=gap;out.ub=b[23].hi;out.status="OPEN";out.port.clear();out.budget=0;out.gain=0;
        if(out.ub<=alpha){out.status="SAFE";out.port="height";return out;}
        if(ports)for(size_t j=0;j<centers.size();++j){
            R dist=0;for(int i=0;i<24;++i)dist=mx(dist,mx(ab(R(gap[i].lo-centers[j][i])),ab(R(gap[i].hi-centers[j][i]))));
            R budget=dist+3*(gap[22].hi+gap[23].hi);
            if(budget<R(1)/1250){out.status="SAFE";out.port="canonical_flow_"+std::to_string(j);out.budget=budget;out.gain=(gap[22].lo+gap[23].lo)/10;return out;}
        }
        return out;
    }
    J oracle_json(const Oracle&o){J j;j.put("status",o.status);if(o.status=="EMPTY"){j.put("reason",o.reason);return j;}
        if(o.contraction_rounds)j.put("contraction_rounds",o.contraction_rounds);
        j.put("height_upper",str(o.ub));j.put("complete_prefix_charts",o.charts?"true":"false");j.add_child("gap_image",intervals_json(o.gap));j.add_child("aux_image",intervals_json(o.aux));
        if(o.status=="SAFE"){j.put("port",o.port);if(o.port!="height"){j.put("budget",str(o.budget));j.put("gain_lower",str(o.gain));}}return j;
    }
    std::pair<std::vector<Row>,std::vector<I>> rows_bounds(const std::vector<I>&aux){
        if(aux.size()!=size_t(nv))throw std::runtime_error("24 auxiliary intervals required");
        std::vector<I>boxes=aux;for(auto&ij:pairs)boxes.push_back(aux[ij.first]*aux[ij.second]);std::vector<Row>rows=base;
        for(size_t pp=0;pp<pairs.size();++pp){int i=pairs[pp].first,j=pairs[pp].second,y=nv+pp;R li=boxes[i].lo,ui=boxes[i].hi,lj=boxes[j].lo,uj=boxes[j].hi;
            std::array<std::array<R,4>,4>terms={{{lj,li,R(-1),R(li*lj)},{uj,ui,R(-1),R(ui*uj)},{R(-uj),R(-li),R(1),R(-li*uj)},{R(-lj),R(-ui),R(1),R(-ui*lj)}}};
            for(auto&term:terms){Row row;row.co[i]+=term[0];row.co[j]+=term[1];row.co[y]+=term[2];row.rhs=term[3];rows.push_back(row);}}
        return {rows,boxes};
    }
    R margin(const std::vector<I>&aux,const J&record){
        std::string kind=record.get<std::string>("kind");if(kind!="C"&&kind!="H")throw std::runtime_error("unknown certificate");
        auto rb=rows_bounds(aux);auto&rows=rb.first;auto&boxes=rb.second;std::vector<R>co(n);R rhs=0;std::set<int>seen;
        auto&weights=record.get_child("weights");if(weights.empty())throw std::runtime_error("empty weights");
        for(auto&entry:weights){auto&pair=entry.second;if(pair.size()!=2)throw std::runtime_error("bad support pair");auto it=pair.begin();Big ii=integer(it->second.data());++it;Big w=integer(it->second.data());
            if(ii<0||ii>=rows.size()||w<=0)throw std::runtime_error("bad row/weight");int i=ii.convert_to<int>();if(!seen.insert(i).second)throw std::runtime_error("duplicate row");
            rhs+=R(w)*rows[i].rhs;for(auto&term:rows[i].co)co[term.first]+=R(w)*term.second;}
        Big t=0;if(kind=="H"){t=integer(record.get<std::string>("objective_weight"));if(t<=0)throw std::runtime_error("bad objective weight");co[fi]-=R(t);}
        for(int i=0;i<n;++i)rhs-=mn(R(co[i]*boxes[i].lo),R(co[i]*boxes[i].hi));if(kind=="H")rhs-=R(t)*alpha;return rhs;
    }
    J request(const J&q){
        std::string mode=q.get<std::string>("mode");if(mode=="identity")return data.get_child("identities");
        if(mode=="margin_aux"){J out;out.put("margin",str(margin(intervals(q.get_child("aux")),q.get_child("record"))));return out;}
        std::vector<I>aux;J out;
        if(mode=="rows_aux"){aux=intervals(q.get_child("aux"));}
        else{
            if(mode=="leaf"&&q.get_optional<std::string>("enclosure"))throw std::runtime_error("leaf enclosure must come from certificate");
            const J &selector=mode=="leaf"?q.get_child("record"):q;
            auto enclosure=selector.get_optional<std::string>("enclosure");
            if(enclosure&&*enclosure!="high_value_v1")throw std::runtime_error("unknown enclosure version");
            bool ports=q.get<bool>("local_ports",true);
            Oracle o=oracle(intervals(q.get_child("box")),ports);
            if(enclosure)o=high_value(o,ports);
            if(mode=="leaf"||mode=="prepare")out.put("status",o.status);else out=oracle_json(o);aux=o.aux;
            if(mode=="leaf"){auto&record=q.get_child("record");std::string kind=record.get<std::string>("kind");
                if(kind=="E"){if(o.status=="OPEN")throw std::runtime_error("uncertified E leaf");out.put("leaf_status",o.status);return out;}
                if(aux.empty())throw std::runtime_error("C/H needs canonical image");R m=margin(aux,record);
                if((kind=="C"&&m>=0)||(kind=="H"&&m>0))throw std::runtime_error("invalid exact leaf margin");out.put("margin",str(m));out.put("leaf_status",kind=="C"?"EMPTY":"SAFE");return out;}
            if(mode=="oracle"||o.status!="OPEN")return out;
            if(mode!="prepare")throw std::runtime_error("unknown operation");
        }
        auto rb=rows_bounds(aux);J rows,rhs,bounds;
        bool exact=mode=="rows_aux";
        for(auto&row:rb.first){J terms;for(auto&term:row.co){J pair;push(pair,scalar(std::to_string(term.first)));push(pair,scalar(exact?str(term.second):std::to_string(0)));if(!exact)pair.back().second.put_value(term.second.convert_to<double>());push(terms,pair);}push(rows,terms);J value;if(exact)value.put_value(str(row.rhs));else value.put_value(row.rhs.convert_to<double>());push(rhs,value);}
        out.add_child(exact?"rows_exact":"rows_float",rows);out.add_child(exact?"rhs_exact":"rhs_float",rhs);
        if(exact)out.add_child("product_bounds",intervals_json(rb.second));
        if(!exact){J center,half;for(auto&b:rb.second){J c,h;c.put_value(R((b.lo+b.hi)/2).convert_to<double>());h.put_value(R((b.hi-b.lo)/2).convert_to<double>());push(center,c);push(half,h);}out.add_child("center",center);out.add_child("half",half);}
        return out;
    }
};
static thread_local std::string create_error;
extern "C" void* b17_create(){try{create_error.clear();return new Engine();}catch(const std::exception&e){create_error=e.what();return nullptr;}}
extern "C" const char* b17_last_error(){return create_error.c_str();}
extern "C" void b17_destroy(void*p){delete static_cast<Engine*>(p);}
extern "C" const char* b17_request(void*p,const char*input){static thread_local std::string response;try{response=encode(static_cast<Engine*>(p)->request(parse(input)));}catch(const std::exception&e){J j;j.put("error",e.what());response=encode(j);}return response.c_str();}
