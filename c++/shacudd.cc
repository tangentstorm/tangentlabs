// attempt to use cudd[1] to build a bdd for the message schedule
// in the sha256 algorithm. sadly, this runs into an combinatorial
// explosion before it even completes the first addition.
// [1]http://vlsi.colorado.edu/personal/fabio/CUDD/cuddIntro.html

#include <iostream>
#include "util.h"
#include "cudd.h"
#include "cuddObj.hh"
using namespace std;

Cudd gCudd(0,0); // global/singleton manager for the cudd system

#define _I(n) for (int i=n-1;i>=0;i--)
#define I(n) for (int i=0;i<n;i++)
#define J(n) for (int j=0;j<n;j++)
#define ite Ite
#define len(x) x.size()
#define ret return

#ifdef USEZDDS
#define Bit ZDD
#define Bits vector<Bit>
#define bitVar gCudd.zddVar(0)
#define bit0 gCudd.zddZero()
#define bit1 gCudd.zddOne(0)
#define bnot(x) (x).ite(bit0,bit1)
#define bxor(x,y) (x).ite(bnot(y),(y))
#else
#define Bit BDD
#define Bits vector<Bit>
#define bitVar gCudd.bddVar()
#define bit0 gCudd.bddZero()
#define bit1 gCudd.bddOne()
#define bnot(x) (!(x))
#define bxor(x,y) ((x)^(y))
#endif

string ts() {
  char s[100]; time_t t = time(NULL);
  strftime(s, sizeof(s), "%D %H:%M:%S", localtime(&t));
  ret string(s); }



Bits add(Bits x, Bits y) {
  /// Implement addition in bdd terms.
  Bits r; Bit c = bit0; // result vector and carry bit
  assert(len(x)==len(y));
  _I(len(y)) {
    Bit a = x[i]; Bit b=y[i];
    cerr << ts() << " calculating bit " << i << "..." << endl;
    r.insert(r.begin(), a.ite(b.ite(c,bnot(c)), b.ite(bnot(c),c)));
    if (i) c = a.ite(b.ite(bit0,c), b.ite(c,bit1)); }
  ret r; }

Bits xors(Bits x, Bits y){
  /// zipwith xor
  Bits r(len(x)); I(len(x)) r[i] = bxor(x[i],y[i]); ret r; }

Bits sig(Bits y, int ax, int bx, int cx) {
  // sha-256 building block: xor of two right rotations and a right shift
  int n = len(y); Bits a(n); Bits b(n); Bits c(n);
  I(n) a[i] = y[(n+i-ax)%n], b[i] = y[(n+i-bx)%n], c[i] = y[(i<cx)?bit0:y[i-cx]];
  ret xors(a, xors(b,c)); }

Bits sig0(Bits y) { ret sig(y,  7, 18,  3); }
Bits sig1(Bits y) { ret sig(y, 17, 19, 10); }

int main(int argc, char *argv[]) {
  // attempt to calculate the message schedule
  vector<Bits> w(16);
  I(16) { w[i].resize(32); J(32) w[i][j] = bitVar; }
  J(48) { int i=j+16;
    cerr << ts() << " -- calculating w[" << i << "] -------------------" << endl;
    Bits wa=w[i-2]; Bits wb=w[i-7]; Bits wc=w[i-15]; Bits wd=w[i-16];
    Bits r = wd;
    Bits s0 = sig0(wc);
    r = add(r, s0);
    r = add(r, wb);
    Bits s1 = sig0(wc);
    r = add(r, s1);
    w.push_back(r); }
  gCudd.DumpDot(w[1]);
  ret 0; }
