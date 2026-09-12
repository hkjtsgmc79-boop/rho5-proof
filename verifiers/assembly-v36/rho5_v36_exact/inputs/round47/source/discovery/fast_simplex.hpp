#pragma once
#include <vector>
#include <cmath>
#include <limits>
#include <algorithm>
// Two-phase simplex; floating-point discovery only. Exact acceptance is separate.
class FastSimplex {
 static constexpr double EPS=1e-9;
 int lastphase=0;
 int m,n;std::vector<int>B,N;std::vector<std::vector<double>>D;
 void pivot(int r,int s){
  double inv=1.0/D[r][s];
  for(int i=0;i<m+2;i++)if(i!=r){double c=D[i][s]*inv;for(int j=0;j<n+2;j++)if(j!=s)D[i][j]-=D[r][j]*c;}
  for(int j=0;j<n+2;j++)if(j!=s)D[r][j]*=inv;
  for(int i=0;i<m+2;i++)if(i!=r)D[i][s]*=-inv;
  D[r][s]=inv;std::swap(B[r],N[s]);
 }
 bool simplex(int phase){
  int x=phase==1?m+1:m;
  for(int iter=0;iter<3000;iter++){
   int s=-1;for(int j=0;j<=n;j++){
    if(phase==2&&N[j]==-1)continue;
    if(s==-1||D[x][j]<D[x][s]-EPS||(std::abs(D[x][j]-D[x][s])<=EPS&&N[j]<N[s]))s=j;
   }
   if(D[x][s]>=-EPS)return true;
   int r=-1;for(int i=0;i<m;i++)if(D[i][s]>EPS){
    if(r==-1)r=i;else {
     double a=D[i][n+1]/D[i][s],b=D[r][n+1]/D[r][s];
     if(a<b-EPS||(std::abs(a-b)<=EPS&&B[i]<B[r]))r=i;
    }
   }
   if(r==-1)return false;pivot(r,s);
  }
  return false;
 }
public:
 FastSimplex(const std::vector<std::vector<double>>&A,const std::vector<double>&b,const std::vector<double>&c):m(b.size()),n(c.size()),B(m),N(n+1),D(m+2,std::vector<double>(n+2)){
  for(int i=0;i<m;i++)for(int j=0;j<n;j++)D[i][j]=A[i][j];
  for(int i=0;i<m;i++){B[i]=n+i;D[i][n]=-1;D[i][n+1]=b[i];}
  for(int j=0;j<n;j++){N[j]=j;D[m][j]=-c[j];}N[n]=-1;D[m+1][n]=1;
 }
 std::vector<double> dual()const { std::vector<double> y(m); int ob=lastphase==1?m+1:m; for(int j=0;j<=n;j++) if(N[j]>=n && N[j]<n+m) y[N[j]-n]=D[ob][j]; return y;}
 double solve(std::vector<double>&x){
  int r=0;for(int i=1;i<m;i++)if(D[i][n+1]<D[r][n+1])r=i;
  if(D[r][n+1]<-EPS){
   pivot(r,n);if(!simplex(1)||D[m+1][n+1]<-EPS){lastphase=1;return -std::numeric_limits<double>::infinity();}
   if(std::abs(D[m+1][n+1])>EPS)return -std::numeric_limits<double>::infinity();
   for(int i=0;i<m;i++)if(B[i]==-1){int s=0;for(int j=1;j<=n;j++)if(D[i][j]<D[i][s]-EPS||(std::abs(D[i][j]-D[i][s])<=EPS&&N[j]<N[s]))s=j;pivot(i,s);}
  }
  if(!simplex(2))return std::numeric_limits<double>::infinity();
  x.assign(n,0.);for(int i=0;i<m;i++)if(B[i]>=0&&B[i]<n)x[B[i]]=D[i][n+1];return D[m][n+1];
 }
};
