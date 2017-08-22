#include<bits/stdc++.h>

#define pb push_back
#define ff first
#define ss second


int const N = 501;
int const M = 10001;

using namespace std;
using vi=vector<int>;
//using clause=set<int>;
//using boolean_formula=list<clause>;

vector<set<int>> Literals;
vector<vector<int>> clauses;

bool is_satisfied[M];

int n, m;
int n_active_clause;

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

    Literals.resize(m+1, set<int>()),
    clauses.resize(n+1, vi()),
    n_active_clause=m;

    for (int i=1; i<=m; ++i) {
        getline(cin,s);
        if (s[0]=='c') {--i; continue;}
        stringstream ss(s);
        int j; ss>>j;
        while(j!=0) {
            Literals[i].insert(j);
            clauses[abs(j)].pb(j>0?i:-i);
            ss>>j;
        }
    }
}

bool unit_resolution(vi& res, vi& removed, map<int, list<int>>& erased)
{
    queue<int> q;

    bool seen[N]={false};
    for (int i=1; i<=m; ++i) {
       if (is_satisfied[i]) continue; 
       if (Literals[i].size()==1) {
           auto j =*Literals[i].begin();
           if (!seen[abs(j)]) q.push(j), seen[abs(j)]=true;
       }
    }

    while(!q.empty()) {

        auto j=q.front();
        q.pop();
        res.pb(j);

        for (auto i: clauses[abs(j)]) {

            if (is_satisfied[abs(i)]) continue;

            if (j*i > 0) removed.pb(abs(i)), is_satisfied[abs(i)]=true, --n_active_clause;
            else {
                i = abs(i);
                erased[-j].pb(i), Literals[i].erase(-j);
                if (Literals[i].size()==0) return false;
                else if (Literals[i].size()==1) {
                    auto x  = *Literals[i].begin();
                    if (!seen[abs(x)]) q.push(x), seen[abs(x)]=true;
                }
            }
        } 
    }

    return true;
}

void condition(int l, vi& removed, map<int, list<int>>& erased)
{
    for (auto i: clauses[abs(l)]) {
        if (is_satisfied[abs(i)]) continue;
        
        if (l*i > 0) removed.pb(abs(i)), is_satisfied[abs(i)]=true, --n_active_clause;
        else {
            i = abs(i);
            erased[-l].pb(i), Literals[i].erase(-l);
        }
    }
}

void backtrack(vi& removed, map<int, list<int>>& erased)
{
    for (auto i: removed)
        is_satisfied[i]=false, ++n_active_clause;

    for (auto& x: erased)
        for (auto& i: x.ss)
            Literals[i].insert(x.ff);
}

int choose_literal()
{
    for (int i=1; i<=m; ++i)
        if (!is_satisfied[i]) return *Literals[i].begin();
}

bool solve(vi&, int d);

bool solve_branch(int l, vi& I, int d)
{
    vi _I;
    vi removed_cond;
    map<int, list<int>> erased_cond;

    condition(l, removed_cond, erased_cond);
    if (solve(_I, d)) {
        I.insert(I.end(), _I.begin(), _I.end());
        I.pb(l);
        return true;
    }

    backtrack(removed_cond, erased_cond);
    return false;
}

bool solve(vi& I, int d=1)
{
    vi removed_unit;
    map<int, list<int>> erased_unit;

    if (!unit_resolution(I, removed_unit, erased_unit)) {
        backtrack(removed_unit, erased_unit);
        return false;
    }

    if (n_active_clause == 0)
        return true;

    auto l = choose_literal();

    if (solve_branch(l, I, d+1)) {
        return true;
    }
    else if (solve_branch(-l, I, d+1)) {
        return true;
    }

    backtrack(removed_unit, erased_unit);
    return false;
}

bool foo(int a, int b) {return abs(a) < abs(b);}

int main()
{
    input();
    vi v;
    if (solve(v)) {
        cout<<"SAT\n";
        sort(v.begin(), v.end(), foo);
        int i=1;
        for (auto it=v.begin(); it!=v.end(); ++it, ++i) {
            while(i<abs(*it)) cout<<i++<<" ";
            cout<<*it<<" ";
        }
        while(i<=n) cout<<i++<<" ";
        cout<<"0";
    }
    else cout<<"UNSAT";
    return 0;
}
