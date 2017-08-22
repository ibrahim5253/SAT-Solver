#include<bits/stdc++.h>

#define pb push_back

int const N = 501;
int const M = 10001;

using namespace std;
using vi=vector<int>;
using clause=set<int>;
using boolean_formula=list<clause>;

vector<bitset<N>> literals;
//vector<bitset<M>> clauses;

int clause_state[M];

int n, m;

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

    literals.resize(2*m+1, bitset<N>()),
//    clauses.resize(2*n+1, bitset<M>());

    for (int i=1; i<=m; ++i) {
        getline(cin,s);
        if (s[0]=='c') {--i; continue;}
        stringstream ss(s);
        int j; ss>>j;
        while(j!=0) {
            if (j<0) literals[(i<<1)-1][-j]=1;//, clauses[(-j<<1)-1][i]=1;
            else literals[i<<1][j]=1;//, clauses[j<<1][i]=1;
            ss>>j;
        }
    }
}

bool unit_resolution(boolean_formula& cnf, vi& res)
{
    queue<int> q;

    for (int i=1; i<=m; ++i) {
       if (literals[(i<<1)-1].count()+literals[i<<1].count()==1) 
           for (int j=1; j<=n; ++j) {
               if (literals[(i<<1)-1][j]) q.push(-j);
               else if (literals[i<<1][j]) q.push(j);
           }
    }

    while(!q.empty()) {

        auto x=q.front();
        q.pop();
        res.pb(x);

        for (auto it=v[abs(x)].begin(), stop=v[abs(x)].end(); it!=stop; ++it) {

            auto& c = **it;

            if (c == cnf.end()) continue;

            c->erase(-x);
            if (c->count(x)) cnf.erase(c), c = cnf.end();
            else if (c->size()==0) return false;
            else if (c->size()==1 and !seen[abs(*(c->begin()))]) 
                q.push(*(c->begin())), seen[abs(*(c->begin()))]=true;
        } 
    }

    return true;
}

boolean_formula condition(const boolean_formula& cnf, int l)
{
    boolean_formula new_cnf(cnf);

    for (auto it=new_cnf.begin(), stop=new_cnf.end(); it!=stop; ) {
        it->erase(-l);
        if (it->count(l)) it = new_cnf.erase(it);
        else ++it;
    }

    return new_cnf;
}


bool solve(boolean_formula&& cnf, vi& I)
{
    if (!unit_resolution(cnf, I))
        return false;

    if (cnf.empty())
        return true;

    auto literal = *(cnf.front().begin());

    vi _I;
    if (solve(condition(cnf,literal), _I)) {
        I.insert(I.end(), _I.begin(), _I.end());
        I.pb(literal);
        return true;
    }
    _I.clear();
    if (solve(condition(cnf,-literal), _I)) {
        I.insert(I.end(), _I.begin(), _I.end());
        I.pb(-literal);
        return true;
    }
    return false;
}

bool foo(int a, int b) {return abs(a) < abs(b);}

int main()
{
    boolean_formula cnf;
    input(cnf);
    cout<<N<<endl;
    vi v;
    if (solve(move(cnf), v)) {
        cout<<"SAT\n";
        sort(v.begin(), v.end(), foo);
        int i=1;
        for (auto it=v.begin(); it!=v.end(); ++it, ++i) {
            while(i<abs(*it)) cout<<i++<<" ";
            cout<<*it<<" ";
        }
        while(i<=N) cout<<i++<<" ";
        cout<<"0";
    }
    else cout<<"UNSAT";
    return 0;
}
