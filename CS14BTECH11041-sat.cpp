#include<bits/stdc++.h>

#define pb push_back
#define ff first
#define ss second
#define mp make_pair

int const N = 1000;
int const M = 1e7;

#define kappa 0

using namespace std;
using vi=vector<int>;
using pii=pair<int, int>;

vector<vi> clauses;
int num_active[M];
vector<vi> present_in(N, vi());


int var_status[N];
int decision_level[N];
int antecedent[N];

int n, m;

inline unsigned int mod(int v)
{
    return abs(v);
}

void input() 
{
    string s;
    while(1) {
        getline(cin,s);
        if (s[0]=='p') break; 
    }

    stringstream ss(s);
    string p, _cnf;
    ss>>p>>_cnf>>n>>m;

    clauses.resize(m+1, vi());

    for (int i=1; i<=m; ++i) {
        getline(cin,s);
        if (s[0]=='c') {--i; continue;}
        stringstream ss(s);
        int j; ss>>j;
        while(j!=0) {
            clauses[i].pb(j);
            present_in[mod(j)].pb(j>0?i:-i);
            ss>>j;
        }

        num_active[i] = clauses[i].size();
    }

    for (int i=1; i<=n; ++i)
        decision_level[i]=-1;
}

void print_clause(int c)
{
    for (auto& l : clauses[c])
        cout<<" "<<l;
    cout<<endl;
}

int get_active_literal(int i)
{
    for (auto& l : clauses[i])
        if (var_status[mod(l)]*l >= 0) return l;
}

bool unit_propagation(int d)
{
    queue<pii> q;
    bool seen[N]{false};
    for  (int i=1; i<=m; ++i) {
        if (num_active[i] == 0) {
            antecedent[kappa]=i;
            return false;
        }
        else if (num_active[i] == 1) {
            int l = get_active_literal(i);
            if (var_status[mod(l)] == 0 and not seen[mod(l)])
                q.push(mp(l, i)), seen[mod(l)]=true;
        }
    }

    while (not q.empty()) {
        auto p = q.front();
        q.pop();

        int x = p.ff, omega = p.ss;
        var_status[mod(x)] = (x > 0 ? 1 : -1);
        decision_level[mod(x)] = d;
        antecedent[mod(x)] = omega;

        bool f=true;

        for (auto& c: present_in[mod(x)])  
            if (c * x < 0) {
                --num_active[mod(c)];
                if (num_active[mod(c)] == 0) {
                    antecedent[kappa] = mod(c);
                    f=false;
                }
                if (num_active[mod(c)] == 1) {
                    int l = get_active_literal(mod(c));
                    if (var_status[mod(l)] == 0 and not seen[mod(l)])
                        q.push(mp(l, mod(c))), seen[mod(l)]=true;
                }
            } 
        if (!f) return false;
    }
    return true;
}

int pick_branching_variable()
{
    int x = 0;
    for (int i=1; i<=n; ++i)
        if (var_status[i] == 0 and present_in[i].size() > present_in[x].size()) 
            x = i;
    return x;
}

bool conflict_analysis(int dl, int& beta)
{
    queue<int> q;
    bool vis[N]{false};
    vi learned_clause;
    for (auto l: clauses[antecedent[kappa]]) {
        if (vis[mod(l)]) continue;
        if (decision_level[mod(l)] < dl or antecedent[mod(l)]==0)
            learned_clause.pb(l);
        else 
            q.push(l);
        vis[mod(l)] = true;
    }

    while (!q.empty()) {

        auto x = q.front();
        q.pop();

        for (auto l: clauses[antecedent[mod(x)]]) {
            if (vis[mod(l)]) continue;
            if (decision_level[mod(l)] < dl or antecedent[mod(l)]==0)
                learned_clause.pb(l);
            else 
                q.push(l);
            vis[mod(l)]=true; 
        }
    }
    
    clauses.pb(learned_clause);
    ++m;

    int c_idx = clauses.size()-1;
    num_active[c_idx] = 0;

    beta = -1;

    for (auto& l : learned_clause)
        present_in[mod(l)].pb(l>0?c_idx:-c_idx),
        beta = max(beta, decision_level[mod(l)]);    

    if (beta != dl) {
        antecedent[kappa] = c_idx;
        return false;
    }
    return true;
}

void backtrack(int d)
{
    for (int i=1; i<=n; ++i) {
        if (decision_level[i] == d) {
            int x = var_status[i];
            for (auto& c: present_in[i])
                if (c*x < 0) 
                    ++num_active[mod(c)],
            var_status[i]=0;
            decision_level[i]=-1;
            antecedent[i]=0;
        }
    }
}

bool search(int d, int& beta)
{
    int x = pick_branching_variable();
    if (x == 0) return true;

    decision_level[mod(x)] = d;
    var_status[mod(x)] = (x > 0 ? 1 : -1);
    for (auto& c: present_in[mod(x)])
        if (c*x < 0) {
            --num_active[mod(c)];
        }


    while (1) {
        if (unit_propagation(d)) {
            if (search(d+1, beta)) return true;
            else if (beta != d) {backtrack(d); return false;}
        }
        else if (not conflict_analysis(d, beta)) {backtrack(d); return false;}
        backtrack(d);
    }
}

bool CDCL()
{
    if (not unit_propagation(0))
        return false;
    
    int beta;
    return search(1, beta);
}

int main()
{
    input();
    if (CDCL()) {
        cout<<"SAT\n";
        for (int i=1; i<=n; ++i)
            cout<<i*var_status[i]<<" ";
        cout<<"0";
    }
    else cout<<"UNSAT";
    return 0;
}
