//Cycle Breaking
#include <iostream>
#include <fstream>
#include <cstring>
#include <vector>
using namespace std;

void help_message() {
    cout << "usage: ./cb <input_file> <output_file>" << endl;
}

struct vertex{
    int num;
    vertex *p;
    int pw;
    int rank;
    int color;
};

struct edge{
    vertex *start;
    vertex *end;
    int weight;
};

class Graph{
    public:
        vector<vector<edge>> adjL;
        vector<vector<edge>> adjF;
        vector<vertex> head;
        vector<edge> A;
        bool dir;
        void initialize(char ud , int vertice , int edges){
            if(ud == 'd'){
                adjL.resize(vertice);
                adjF.resize(201);
                dir = 1;
            }
            else{
                adjF.resize(201);
                dir = 0;
            }
            int size = vertice;
            head.resize(vertice);
            for(int i = 0 ; i < vertice ; i++){
                vertex j;
                j.num = i;
                head[i] = j;
            }
        }

        void buildEdge(int start , int end , int weight){
            if(dir == 1) adjL[start].push_back({&head[start] , &head[end] , weight});
            else adjF[100 - weight].push_back({&head[start] , &head[end] , weight});
        }

        void make_set(vertex *x){
            x->p = x;
            x->rank = 0;
        }

        void Link(vertex *x , vertex *y){
            if(x->rank > y->rank) y->p = x;
            else{
                x->p = y;
                if(x->rank == y->rank) y->rank += 1;
            }
        }

        vertex *find_set(vertex *x){
            if(x != x->p) x->p = find_set(x->p);
            return x->p;
        }

        void Union(vertex *x , vertex *y){
            Link(find_set(x) , find_set(y));
        }

        vector<edge> MaxST_Kruskal(){
            for(int i = 0 ; i < head.size() ; i++) make_set(&head[i]);
            // for(vector<edge> x:adjF){
            //     for(edge y:x){
            //         if(find_set(y.start) != find_set(y.end)) Union(y.start , y.end);
            //         else A.push_back(y);
            //     }
            // }
            for(int i = 0 ; i < adjF.size() ; i++){
                for(int j = 0 ; j < adjF[i].size() ; j++){
                    if(find_set(adjF[i][j].start) != find_set(adjF[i][j].end)) Union(adjF[i][j].start , adjF[i][j].end);
                    else A.push_back(adjF[i][j]);
                }
            }
            return A;
        }

        vector<edge> DFS(){
            for(int i = 0 ; i < head.size() ; i++){
                head[i].color = 0;
                head[i].p = nullptr;
            }
            for(int i = 0 ; i < head.size() ; i++){
                //cout << head.size() << endl;
                if(head[i].color == 0){
                    cout << i << endl;
                    head[i].p = &head[i];
                    DFS_visit(&head[i]);
                }
            }
            return A;
        }

        vertex* DFS_visit(vertex *u){
            u->color = 1;
            vertex* s;
            for(int i = 0 ; i < adjL[u->num].size() ; i++){
                if(adjL[u->num][i].end->color == 0){
                    adjL[u->num][i].end->p = u;
                    adjL[u->num][i].end->pw = adjL[u->num][i].weight;
                    cout << "te" << endl;
                    s = DFS_visit(adjL[u->num][i].end);
                }
                else if(adjL[u->num][i].end->color == 1){
                    cout << "gray" << endl;
                    vertex* temp = adjL[u->num][i].end;
                    int x = adjL[u->num][i].weight;
                    //cout << adjL[u->num][i].end->num << endl;
                    s = backTrace(u , temp , x);
                    //cout << "ttt" << endl;
                }
                if(s->num == u->num){
                    //cout << "asd" << endl;
                    if(adjL[u->num][i].end->color != 2) i--;
                }
                else{
                    //cout << "test" << endl;
                    u->p = nullptr;
                    u->color = 0;
                    return s;
                }
                cout << i << endl;
                //cout << "size=" << adjL[u->num].size() << endl;
            }
            u->color = 2;
            //cout << u->color << endl;
            return u->p;
        }

        vertex* backTrace(vertex *u , vertex* temp , int x){
            //cout << "x=" << x << endl;
            vertex* s = u;
            vertex* e = temp;
            cout << u->num << ' ' << u->p->num << endl;
            int i = 0;
            while(u != temp){
                //cout << "test" << u->pw << endl;
                if(u->pw < x){
                    x = u->pw;
                    s = u->p;
                    e = u;
                    cout << "ab" << endl;
                }
                //cout << u->num << ' ' << u->p->num << endl;
                i++;
                u = u->p;
            }
            cout << "here" << x << endl;
            //cout << adjL[s->num].size() << endl;
            for(int i = 0;i < adjL[s->num].size();i++){
                if(adjL[s->num][i].end == e) adjL[s->num].erase(adjL[s->num].begin() + i);
            }
            cout << adjL[s->num].size() << endl;
            A.push_back({s , e , x});
            
            return s;
        }

        // void removeEdge(){

        // }
};

int main(int argc , char* argv[]){
    if(argc != 3){
       help_message();
	   return 0;
    }
	fstream fin(argv[1]);
    char ud;
    fin >> ud;
    int n , m;
    fin >> n >> m;
    Graph g;
    g.initialize(ud , n , m);
	int a , b , c;
    while (fin >> a >> b >> c){
        g.buildEdge(a , b , c);
    }
    vector<edge> out;
    vector<edge> out1;
    vector<edge> out2;
    if(g.dir == 1){
        //out1 = g.DFS();
        out = g.DFS();
    }
    else out = g.MaxST_Kruskal();

    fstream fout;
    fout.open(argv[2],ios::out);
    if(out.size() == 0){
        fout << '0' << endl;
    }
    else{
        int count = 0;
        for(int i = 0 ; i < out.size() ; i++) count += out[i].weight;
        fout << count << endl;
        for(int i = 0 ; i < out.size() ; i++){
            fout << out[i].start->num << ' ' << out[i].end->num << ' ' << out[i].weight << endl;
        }
    }
    fin.close();
    fout.close();
	return 0;
}