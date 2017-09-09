#include<bits/stdc++.h>

#define pb push_back
#define ff first
#define ss second

#define DEBUG

int const N = 501;
int const M = 10001;

#define kappa 0

using namespace std;
using vi=vector<int>;
using pii=pair<int, int>;

vector<vi> clauses;
vector<pii> watchers;

int literal_count[N][2];

bool foo(int a, int b)
{
    return max(literal_count[a][0], literal_count[a][1]) > max(literal_count[b][0], literal_count[b][1]);
}

int var_status[N];
int decision_level[N];
int antecedent[N];
set<int> being_watched[N][2];
unordered_set<int> implied_literals;
int dl=0; // current decision level
set<int, bool(*)(int,int)> unassigned_vars(foo);

int n, m;

inline unsigned int mod(int v)
{
/*    int const mask = v >> sizeof(int)*sizeof(char)-1;
    return (v^mask)-mask;
    */
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

    clauses.resize(m+1, vi()),
    watchers.resize(m+1, pii());

    for (int i=1; i<=m; ++i) {
        getline(cin,s);
        if (s[0]=='c') {--i; continue;}
        stringstream ss(s);
        int j; ss>>j;
        while(j!=0) {
            clauses[i].pb(j);
            ss>>j;
            ++literal_count[mod(j)][j>0];
        }
        watchers[i] = {0, clauses[i].size()-1};
        auto f=clauses[i].front(), b=clauses[i].back();
        being_watched[mod(f)][f>0].insert(i);
        being_watched[mod(b)][b>0].insert(i);

        if (clauses[i].size() == 1)
            implied_literals.insert(f);
    }

    for (int i=1; i<=n; ++i)
        unassigned_vars.insert(i);
    
    for (int i=1; i<=n; ++i)
        decision_level[i]=-1;
}

void print_clause(int c)
{
    for (auto& l : clauses[c])
        cout<<" "<<l;
    cout<<endl;
}

bool assign(int x)
{
#ifdef DEBUG
    cout<<"Assigning literal "<<x<<endl;
#endif
    var_status[mod(x)] = (x>0?1:-1);
    unassigned_vars.erase(mod(x));
    auto affected_clauses = being_watched[mod(x)][x<0];

    bool flag=true;
    for (auto& c: affected_clauses) {

#ifdef DEBUG
        cout<<"Clause "<<c<<" has been affected:";print_clause(c);
#endif
        int &p1=watchers[c].ff, &p2=watchers[c].ss;
        int k = clauses[c].size();
        auto& cl = clauses[c];
        
        if (var_status[mod(cl[p1])]*cl[p1] < 0 and var_status[mod(cl[p2])]*cl[p2] < 0) {
        }
        if (cl[p1]==-x) {
            p1=(p2+1)%k;
            while (p1!=p2 and var_status[mod(cl[p1])]*cl[p1] < 0)
                p1=(p1+1)%k;
        }
        else {
            p2=(p1+1)%k;
            while (p1!=p2 and var_status[mod(cl[p2])]*cl[p2] < 0)
                p2=(p2+1)%k;
        }
        if (p1==p2) {
            if (var_status[mod(cl[p1])]==0) {
#ifdef DEBUG
                cout<<"Clause "<<c<<" is unit. "<<cl[p1]<<" is implied."<<endl;
#endif
                implied_literals.insert(cl[p1]), antecedent[mod(cl[p1])]=c;
            }
            else if (var_status[mod(cl[p1])]*cl[p1] < 0) {
#ifdef DEBUG
                cout<<"Clause "<<c<<" is null"<<endl;
#endif
                antecedent[kappa] = c;
                flag = false;
            }
            p1=(p2+1)%k;
        }

        being_watched[mod(x)][x<0].erase(c);
        being_watched[mod(cl[p1])][cl[p1]>0].insert(c);
        being_watched[mod(cl[p2])][cl[p2]>0].insert(c);

        if (flag==false) return false;
#ifdef DEBUG
        cout<<"P1 points to "<<cl[p1]<<endl;
        cout<<"P2 points to "<<cl[p2]<<endl;
#endif
    }
    return flag;
}

bool unit_propagation()
{
    while (!implied_literals.empty()) {
        auto x = *implied_literals.begin();
        implied_literals.erase(implied_literals.begin());

        decision_level[mod(x)]=0;
        for (auto& l: clauses[antecedent[mod(x)]]) {
            if (l!=x)
                decision_level[mod(x)] = max(decision_level[mod(x)], decision_level[mod(l)]);
        }

        //cout<<"Decision level of "<<x<<": "<<decision_level[mod(x)]<<endl;

        if (!assign(x)) {
            implied_literals.clear();return false;
        }
    }
    return true;
}

int pick_branching_variable()
{
    /*
    if (unassigned_vars.empty()) return 0;
    auto x = *unassigned_vars.begin();
    if (literal_count[x][0] > literal_count[x][1])
        return -x;
    return x;
    */
    for (int i=1; i<=n; ++i)
        if (var_status[i] == 0) return i;
    return 0;
}

int conflict_analysis()
{
    queue<int> q;
    bool vis[N]{};
    unordered_set<int> learned_clause;
#ifdef DEBUG
    cout<<"Conflicting clause, "<<antecedent[kappa]<<":";
    for (auto l: clauses[antecedent[kappa]])
        cout<<" "<<l;
    cout<<endl;
#endif
    for (auto l: clauses[antecedent[kappa]]) 
        if (decision_level[mod(l)] < dl or antecedent[mod(l)]==0)
            learned_clause.insert(l);
        else
            vis[mod(l)]=true, q.push(l);

    while (!q.empty()) {

        auto x = q.front();
        q.pop();

        for (auto l: clauses[antecedent[mod(x)]]) {
            if (decision_level[mod(l)] < dl or antecedent[mod(l)]==0)
                learned_clause.insert(l);
            else if (!vis[mod(l)]) 
                vis[mod(l)]=true, q.push(l);
        }
    }
    
    vi new_clause(learned_clause.begin(), learned_clause.end());    
    clauses.pb(new_clause);

    int p1 = 0, p2 = new_clause.size()-1; 

    int c_idx = clauses.size()-1;

    int beta = -1, max_dl = -1;

    for (auto i = 0; i<new_clause.size(); ++i) {
        auto l = new_clause[i];
        ++literal_count[mod(l)][l>0];
        if (decision_level[mod(l)] > max_dl) beta = max_dl, max_dl = decision_level[mod(l)];
        else if (decision_level[mod(l)] < max_dl) beta = max(beta, decision_level[mod(l)]);

        if (decision_level[mod(l)] == dl) {
            implied_literals.insert(l), p1=i, antecedent[mod(l)]=c_idx, decision_level[mod(l)]=-1;
         //   cout<<"Antecedent of "<<l<<", "<<c_idx<<":",print_clause(c_idx);
        }
    }

    if (p1==p2) p1 = (p2+1)%new_clause.size();

    being_watched[mod(new_clause[p1])][new_clause[p1]>0].insert(c_idx);
    being_watched[mod(new_clause[p2])][new_clause[p2]>0].insert(c_idx);

    watchers.pb({p1, p2});

#ifdef DEBUG 
    cout<<"New clause learnt:";
    for (auto &l : new_clause)
        cout<<" "<<l;
    cout<<endl;
#endif
    if (beta == -1) return max_dl - 1;
    return beta;
}

void backtrack(int beta)
{
    for (int i=1; i<=n; ++i)
        if (decision_level[i] > beta)
            var_status[i] = 0, decision_level[i]=-1, antecedent[i]=0, unassigned_vars.insert(i);
}

bool CDCL()
{
    if (not unit_propagation())
        return false;

    int x;
    while ((x = pick_branching_variable())!=0) {
#ifdef DEBUG
        cout<<"Branching on: "<<x<<endl;
#endif
        decision_level[mod(x)]=++dl;
        assign(x);
        while (not unit_propagation()) {
#ifdef DEBUG
            cout<<"BCP failure"<<endl;
#endif
            if (dl == 0) return false;
            auto beta = conflict_analysis();
#ifdef DEBUG
            cout<<"Conflict. Backtracking to "<<beta<<" from "<<dl<<endl;
#endif
            backtrack(beta);
            dl = beta;
        }
    }

    return true;
}

int main()
{
    input();
    if (CDCL()) {
        cout<<"SAT\n";
        for (int i=1; i<=n; ++i)
            cout<<i*var_status[i]<<(i<n?" ":"");
    }
    else cout<<"UNSAT";
    cout<<"\n";
    return 0;
}
