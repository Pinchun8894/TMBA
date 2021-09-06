#include <iostream>
#include <fstream>
#include <vector>
#include <math.h>
#include <cstring>
#include "sat.h"
#include <ctime>
#include "Graph.h"
using namespace std;
//(a1*...*an)->f can be written as (~a1->~f)(~a2->~f)...(~an->f)(a1...an->f)
//create clauses (a1+~f)(a2+~f)...(an+~f)(~a1+~a2+...+~an+f)
//20210426:when k is given , vertices with edges less than k - 1 can be neglected.

class Gate{
public:
   Gate(unsigned i = 0): _gid(i) {}
   ~Gate() {}

   Var getVar() const { return _var; }
   void setVar(const Var& v) { _var = v; }

private:
   unsigned   _gid;  // for debugging purpose...
   Var        _var;
};

vector<Gate *> gates;
int numGates;

int reduceVertice(int k , Graph* g){
   vector<int> record;
   for(int i = 0 ; i < g->adjL2.size() ; i++) cout << "BEFORE: " <<  g->adjL2[i].size() << endl;
   for(int i = 0 ; i < g->adjL2.size() ; i++){
      if(g->adjL2[i].size() < (k - 1)){
         record.push_back(i);
         for(int j = 0 ; j < g->adjL.size() ; j++){
            for(int m = 0 ; m < g->adjL[j].size() ; m++){
               if(g->adjL[j][m].end->index == i){
                  g->adjL[j].erase(g->adjL[j].begin() + m);
                  break;
               }
               if(g->adjL[j][m].start->index == i){
                  for(int x = 0 ; g->adjL[j].size() != 0 ; x++) g->adjL[j].erase(g->adjL[j].begin());
                  break;
               }
            }
         }
      }
   }
   vector<int> temp;
   for(int i = 0 ; i < g->head.size() ; i++) temp.push_back(i);
   for(int i = 0 ; i < record.size() ; i++){
      g->adjL.erase(g->adjL.begin() + record[i] - i);
      temp.erase(temp.begin() + record[i] - i);
   }
   cout << "headsize = " << g->head.size() << endl;
   cout << "tempsize = " << temp.size() << endl;
   for(int i = 0 ; i < temp.size() ; i++){
      for(int j = 0 ; j < g->adjL.size() ; j++){
         for(int m = 0 ; m < g->adjL[j].size() ; m++){
            if(g->adjL[j][m].start->index == temp[i]) g->adjL[j][m].start = &(g->head[i]);
            if(g->adjL[j][m].end->index == temp[i]) g->adjL[j][m].end = &(g->head[i]);
         }
      }
   }

   //for(int i = 0 ; i < g->adjL.size() ; i++) cout << "AFTER: " << g->adjL[i].size() << endl;

   int counter_new = 0;
   for(int i = 0 ; i < g->adjL.size() ; i++) counter_new += g->adjL[i].size();
   int a = g->adjL.size();
   int b = a*(a - 1)/2 - counter_new;
   g->size = a;
   g->e = b;
   g->head.resize(a);
   return a;
}

void reCheck(int k , Graph* g){
   g->adjL2.resize(g->size);
   for(int i = 0 ; i < g->adjL2.size() ; i++) g->adjL2[i].clear();
   for(int i = 0 ; i < g->adjL2.size() ; i++){
      for(int j = 0 ; j < g->adjL2.size() ; j++){
         if(i != j) g->adjL2[i].push_back({&(g->head[i]) , &(g->head[j])});
      }
   }

   for(int i = 0 ; i < g->adjL.size() ; i++){
      for(int j = 0 ; j < g->adjL[i].size() ; j++){
         int st = g->adjL[i][j].start->index;
         int en = g->adjL[i][j].end->index;
         for(int m = 0 ; m < g->adjL2[st].size() ; m++){
            if(g->adjL2[st][m].end->index == en){
               g->adjL2[st].erase(g->adjL2[st].begin() + m);
               break;
            }
         }
         for(int m = 0 ; m < g->adjL2[en].size() ; m++){
            if(g->adjL2[en][m].end->index == st){
               g->adjL2[en].erase(g->adjL2[en].begin() + m);
               break;
            }
         }
      }
   }
}

void initCircuit(int k , Graph* g){ //send by const referrences(read only but no copy)
   // Init gates
   int V = g->numofV();
   int E = g->numofE();
   numGates = k * (V + 1) + (k*(k - 1)/2) * (pow(V , 2) - (E * 2)) + 1;
   //cout << "numGates = " << numGates << endl;
   for(int i = 0 ; i < numGates ; i++) gates.push_back(new Gate(i));
}

void genProofModel(SatSolver& s , int k , Graph* g){
   // Allocate and record variables; No Var ID for POs
   int V = g->numofV();
   int E = g->numofE();
   for (size_t i = 0, n = gates.size(); i < n; ++i) {
      Var v = s.newVar();
      gates[i]->setVar(v);
   }

   vector<Var> va;
   vector<bool> nega;
   int curGate = V * k;

   if(V < k){
      va.push_back(gates[0]->getVar());
      va.push_back(gates[0]->getVar());
      nega.push_back(true);
      nega.push_back(false);
      s.addAigCNF(gates[gates.size() - 1]->getVar() , va , nega);
      cout << "V < k" << endl;
   }
   else{
      for(int i = 0 ; i < k ; i++){
         for(int j = 0 ; j < V ; j++){
            va.push_back(gates[V * i + j]->getVar());
            nega.push_back(true);
         }
         s.addAigCNF(gates[curGate]->getVar() , va , nega);
         curGate++;
         va.clear();
         nega.clear();
      }

      for(int i = 0 ; i < V ; i++){
         for(int j = 0 ; j < k ; j++){
            for(int m = j + 1 ; m < k ; m++){
               va.push_back(gates[V*j + i]->getVar());
               va.push_back(gates[V*m + i]->getVar());
               nega.push_back(false);
               nega.push_back(false);
               s.addAigCNF(gates[curGate]->getVar() , va , nega);
               curGate++;
               va.clear();
               nega.clear();
            }
         }
      }

      for(int i = 0 ; i < g->adjL.size() ; i++){
         for(int j = 0 ; j < g->adjL[i].size() ; j++){
            int st = g->adjL[i][j].start->index;
            int en = g->adjL[i][j].end->index;
            for(int m = 0 ; m < k ; m++){
               for(int n = m + 1 ; n < k ; n++){
                  va.push_back(gates[V*m + st]->getVar());
                  va.push_back(gates[V*n + en]->getVar());
                  nega.push_back(false);
                  nega.push_back(false);
                  s.addAigCNF(gates[curGate]->getVar() , va , nega);
                  curGate++;
                  va.clear();
                  nega.clear();
                  va.push_back(gates[V*m + en]->getVar());
                  va.push_back(gates[V*n + st]->getVar());
                  nega.push_back(false);
                  nega.push_back(false);
                  s.addAigCNF(gates[curGate]->getVar() , va , nega);
                  curGate++;
                  va.clear();
                  nega.clear();
               }
            }
         }
      }
   }
   

   for(int i = V * k ; i < curGate ; i++){
      va.push_back(gates[i]->getVar());
      nega.push_back(true);
   }
   s.addAigCNF(gates[curGate]->getVar() , va , nega);

   cout << "model complete!" << endl;
}

void reportResult(const SatSolver& solver, bool result , int V , int k){
   solver.printStats();
   cout << (result? "SAT" : "UNSAT") << endl;
   if(result){
      int counter = 0;
      for(size_t i = 0 ; i < V * k; ++i){
         counter++;
         cout << solver.getValue(gates[i]->getVar()) << " ";
         if(counter % V == 0) cout << endl;
      }
   }
   cout << endl;
}

int main(int argc , char* argv[]){
   clock_t start , end;
   start = clock();
   fstream fin(argv[1]);
   int n , m;
   fin >> n >> m;
   Graph g;
   g.initialize(n , m);
   g.buildComplete(n);
	int a , b;
   while (fin >> a >> b){
      g.buildNonEdge(a , b);
   }

   int x;
   cin >> x;

   reduceVertice(x , &g);
   
   int counter = 0;
   while(true){
      counter ++;
      int before = g.size;
      reCheck(x , &g);
      int after = reduceVertice(x , &g);
      if(before == after) break;
   }
   cout << "counter = " << counter << endl;

   int V = g.numofV();
   int E = g.numofE();

   initCircuit(x , &g);

   SatSolver solver;
   solver.initialize();
   //
   genProofModel(solver , x , &g);

   bool result;
   solver.assumeProperty(gates[gates.size() - 1]->getVar() , true);
   result = solver.assumpSolve();
   reportResult(solver, result , V , x);
   end = clock();
   double time = end - start;
   cout << "time = " << time/CLOCKS_PER_SEC << endl;
}