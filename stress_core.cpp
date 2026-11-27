// Independent exact-budget maximisation on an oriented tree. No closed star formula
// enters the solver. Compile with c++ -O2 -std=c++17 stress_core.cpp -o stress_core.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

using Int = std::int64_t;
using Scores = std::vector<Int>;
using Table = std::array<Scores,3>;
constexpr Int impossible = -(Int{1}<<60);
enum Mark { minusState, plusState, emptyState };

struct Vertex {
    int parent;
    bool pointsToParent;
    Int outWeight, inWeight;
};

void demand(bool test, const std::string &reason) {
    if (!test) throw std::runtime_error(reason);
}

Scores convolve(const Scores &a, const Scores &b, int limit) {
    const int length = std::min<int>(limit+1,a.size()+b.size()-1);
    Scores result(length,impossible);
    for (int i=0; i<int(a.size()); ++i) {
        if(a[i]==impossible) continue;
        for (int j=0; j<int(b.size()) && i+j<length; ++j) {
            if(b[j]!=impossible) result[i+j]=std::max(result[i+j],a[i]+b[j]);
        }
    }
    return result;
}

Scores solve(const std::vector<Vertex> &tree, int limit) {
    std::vector<std::vector<int>> children(tree.size());
    for(int v=1;v<int(tree.size());++v) children.at(tree[v].parent).push_back(v);
    std::vector<Table> table(tree.size());
    for(int v=int(tree.size())-1;v>=0;--v) {
        const Vertex &parent=tree[v];
        table[v]={Scores{parent.outWeight},Scores{parent.inWeight},
                  Scores{impossible,parent.inWeight+parent.outWeight}};
        for(int child:children[v]) {
            const Table &ct=table[child];
            for(int ps=minusState;ps<=emptyState;++ps) {
                Scores compatible;
                for(int cs=minusState;cs<=emptyState;++cs) {
                    int from=tree[child].pointsToParent ? cs : ps;
                    int to=tree[child].pointsToParent ? ps : cs;
                    if(from==plusState && to==minusState) continue;
                    if(compatible.size()<ct[cs].size()) compatible.resize(ct[cs].size(),impossible);
                    for(int j=0;j<int(ct[cs].size());++j)
                        compatible[j]=std::max(compatible[j],ct[cs][j]);
                }
                table[v][ps]=convolve(table[v][ps],compatible,limit);
            }
            table[child]=Table{};
        }
    }
    Scores result(limit+1,impossible);
    for(const Scores &row:table[0])
        for(int i=0;i<int(row.size()) && i<=limit;++i) result[i]=std::max(result[i],row[i]);
    return result;
}

struct Design { Scores f, balanced; };
Design design(const std::string &word) {
    int t=0;
    while(t<int(word.size()) && word[t]=='-') ++t;
    int h=int(word.size())+1-t;
    Int slope=h;
    Scores v(h+1),f(h+1),balanced;
    for(int j=1;j<=h;++j) {
        v[j]=v[j-1]+slope;
        if(j<h) slope += word[t+j-1]=='+' ? 1 : -1;
    }
    const Int amp=2*v[h]+1;
    for(int s=1;s<=h;++s) f[s]=amp*(2*s-1)+v[s];
    for(int i=0;i<t;++i) balanced.push_back(2*f[h]+t-i);
    return {f,balanced};
}

std::vector<Vertex> build(const Design &d) {
    std::vector<Vertex> tree={{-1,false,0,0}};
    for(int s=1;s<int(d.f.size());++s) {
        int center=tree.size();
        tree.push_back({0,false,d.f[s],0});
        for(int i=0;i<s;++i) tree.push_back({center,true,d.f.back(),2*d.f.back()});
    }
    for(Int w:d.balanced) tree.push_back({0,false,w,w});
    return tree;
}

Scores prediction(const Design &d) {
    Int h=int(d.f.size())-1, t=d.balanced.size(), b=d.f.back();
    Int base=b*h*(h+1);
    for(Int w:d.balanced) base+=w;
    Scores out;
    Int prefix=0;
    for(int r=0;r<=h+t;++r) {
        if(r>0 && r<=t) prefix+=d.balanced[r-1];
        int k=std::max<Int>(0,r-t);
        out.push_back(base+prefix+b*k+d.f[k]);
    }
    return out;
}

struct Audit {int words=0; Int budgets=0, vertices=0; int maxLength=0;};
void check(const std::string &word, Audit &audit) {
    auto d=design(word);
    auto vertices=build(d);
    auto observed=solve(vertices,int(word.size())+1);
    auto predicted=prediction(d);
    demand(observed==predicted,"wrong optimum for "+word);
    for(int i=0;i<int(word.size());++i) {
        Int second=observed[i]+observed[i+2]-2*observed[i+1];
        demand((word[i]=='+' && second>0)||(word[i]=='-' && second<0),"wrong curvature for "+word);
    }
    ++audit.words; audit.budgets+=observed.size(); audit.vertices+=vertices.size();
    audit.maxLength=std::max(audit.maxLength,int(word.size()));
}

int main() {
    Audit all,large;
    for(int n=1;n<=12;++n) {
        for(unsigned bits=0;bits<(1U<<n);++bits) {
            std::string word(n,'-');
            for(int i=0;i<n;++i) if(bits&(1U<<i)) word[i]='+';
            check(word,all);
        }
    }
    std::mt19937_64 rng(0xc0ffeedULL);
    for(int n:{17,32,63,96,128,191,256}) {
        for(int k=0;k<13;++k) {
            std::string word(n,'-');
            for(int i=0;i<n;++i) {
                bool positive=false;
                switch(k) {
                    case 0: positive=true; break;
                    case 1: break;
                    case 2: positive=i==n-1; break;
                    case 3: positive=i==0; break;
                    case 4: positive=(i%2)==0; break;
                    case 5: positive=(i%2)==1; break;
                    case 6: positive=(i>=n/2); break;
                    case 7: positive=(i<n/2); break;
                    default: positive=(rng()&1U)!=0;
                }
                if(positive) word[i]='+';
            }
            check(word,large);
        }
    }
    // Remove superadditivity. Two whole stars now outperform the proposed single star.
    Design nonSuper{{0,5,5,5},{}};
    auto got=solve(build(nonSuper),3),wrong=prediction(nonSuper);
    demand(got[3]>wrong[3],"superadditivity control did not fail");
    // Set the gain of the first balanced label below the largest main increment.
    Design weak{{0,1,4},{1}};
    auto actual=solve(build(weak),3),priority=prediction(weak);
    demand(actual[1]>priority[1],"priority control did not fail");
    std::cout << "{\n  \"all_words_through_length\": "<<all.maxLength<<",\n  \"short_words\": "<<all.words
              <<",\n  \"short_exact_budgets\": "<<all.budgets<<",\n  \"long_words\": "<<large.words
              <<",\n  \"maximum_long_length\": "<<large.maxLength<<",\n  \"long_exact_budgets\": "<<large.budgets
              <<",\n  \"total_core_vertices_processed\": "<<all.vertices+large.vertices
              <<",\n  \"non_superadditive_at_three_actual_predicted\": ["<<got[3]<<","<<wrong[3]
              <<"],\n  \"weak_balanced_at_one_actual_predicted\": ["<<actual[1]<<","<<priority[1]<<"]\n}\n";
}
