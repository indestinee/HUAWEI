#include "deploy.h"
#include <cstdio>
#include <cstring>
#include <algorithm>
#include <queue>
#include <cmath>
#include <string>
#include <iostream>
using namespace std;
#define DEBUG
#define prev prevDSJAIOIOWD
#define TIME (double(clock())/double(CLOCKS_PER_SEC))
const int maxm = 210000, inf = 0x63636363, maxn = 4024, my_favority_number = 91203;
const double log_rand_max = log(RAND_MAX), rate = 1;
int node_num, edge_num, sink_num, server_cost, totle_flow, ans, source, sink, nume, flow, used, st[maxm], ed[maxm], limit[maxm], cost[maxm], sink_node[maxn], father[maxn], need[maxn], g[maxn], dist[maxn], prev[maxn], pree[maxn], vis[maxn], out_flow[maxn], id[maxn], que[maxn], qst, qed, limit_best_time, each_flow[maxn], score[maxn], max_sink, is_near_sink[maxn], last_sink, tmp_vec[maxn], tmp_num;
string res;
vector<int> out, source_vec, rest_vec, best_vec, sink_vec;
bool inque[maxn];
char buff[1 << 20];
class edge{/*{{{*/
public:
    edge () { }
    edge (const int &v, const int &f, const int &w, const int &nxt): v(v), f(f), w(w), nxt(nxt) { }
    int v, f, w, nxt;
} e[maxm];/*}}}*/
inline string itoa(int x) {/*{{{*/
    if (x == 0)
        return "0";
    string ret = "";
    while (x) {
        ret += char(x % 10 + '0');
        x /= 10;
    }
    reverse(ret.begin(), ret.end());
    return ret;
}/*}}}*/
inline void init(char *topo[MAX_EDGE_NUM]) {/*{{{*/
	sscanf(topo[0], "%d%d%d", &node_num, &edge_num, &sink_num);
    sscanf(topo[2], "%d", &server_cost);
    int TMP = 0;
    for (int i = 0; i < edge_num; i++) {
        sscanf(topo[i + 4], "%d%d%d%d", &st[i], &ed[i], &limit[i], &cost[i]);
        out_flow[st[i]] += limit[i];
        out_flow[ed[i]] += limit[i];
    }
    for (int i = 0; i < sink_num; i++) {
        sscanf(topo[i + 5 + edge_num], "%d%d%d", &sink_node[i], &father[i], &need[i]);
        totle_flow += need[i];
        out_flow[father[i]] += need[i];
        is_near_sink[father[i]] = 1;
    }
    for (int i = 0; i < node_num; i++)
        tmp_vec[tmp_num++] = out_flow[i];
    sort(tmp_vec, tmp_vec + tmp_num);
    TMP = tmp_vec[int(tmp_num * 0.98)];
    if (false) {
        for (int i = 0; i < edge_num; i++) {
            if (is_near_sink[ed[i]] && !is_near_sink[st[i]] && out_flow[st[i]] > TMP)
                is_near_sink[st[i]] = 2;
            if (!is_near_sink[ed[i]] && is_near_sink[st[i]] && out_flow[ed[i]] > TMP)
                is_near_sink[ed[i]] = 2;

        }
    }
}/*}}}*/
inline void addedge(const int &u, const int &v, const int &c, const int &w) {/*{{{*/
    if (w > server_cost)
        return;
    e[++nume] = edge(v, c, w, g[u]);
	g[u] = nume;
    e[++nume] = edge(u, 0, -w, g[v]);
    g[v] = nume;
}/*}}}*/
inline void build_edge() {/*{{{*/
    source = node_num + sink_num;
    sink = source + 1;
    nume = 1;
    flow = 0;
    memset(g, 0, sizeof g);
    for (auto i: source_vec)
        addedge(source, i, inf, 0);
    for (int i = 0; i < edge_num; i++) {
        addedge(st[i], ed[i], limit[i], cost[i]);
        addedge(ed[i], st[i], limit[i], cost[i]);
    }
    for (int i = 0; i < sink_num; i++) {
        addedge(i + node_num, sink, inf, 0);
        addedge(father[i], i + node_num, need[i], 0);
    }
}/*}}}*/
inline bool spfa() {/*{{{*/
    memset(dist, 0x63, sizeof dist);
    //	que.push(source);
    qst = qed = 0;
    que[qed++] = source;
    dist[source] = 0;
    inque[source] = true;
    //	while (!que.empty()) {
    while (qst < qed) {
        //		int u = que.front();
        //        que.pop();
        int u = que[qst++];
        if (qst == maxn)
            qst = 0;
        inque[u] = false;
        int tmp_weight;
        for (int i = g[u]; i; i = e[i].nxt) {
            int v = e[i].v;
            if (e[i].f > 0 && (tmp_weight = dist[u] + e[i].w) < dist[v] && (tmp_weight < server_cost)) {
                dist[v] = tmp_weight;
                prev[v] = u;
                pree[v] = i;
                if (!inque[v]) {
                    inque[v] = true;
                    //                    que.push(v);
                    que[qed++] = v;
                    if (qed == maxn)
                        qed = 0;
                }
            }
        }
    }
    return dist[sink] < inf;
}/*}}}*/
inline int argument() {/*{{{*/
    int u = sink, delta = inf;
    while (u != source) {
        if (e[pree[u]].f < delta)
            delta = e[pree[u]].f;
        u = prev[u];
    }
    u = sink;
    while (u != source) {
        e[pree[u]].f -= delta;
        e[pree[u] ^ 1].f += delta;
        if (pree[u] & 1) {
            each_flow[prev[u]] -= delta;
        } else {
            each_flow[prev[u]] += delta;
        }
        if (prev[u] == source && !vis[u])
            used += (vis[u] = 1);
        u = prev[u];
    }
    flow += delta;
    return dist[sink] * delta;
}/*}}}*/
int min_cost_flow() {/*{{{*/
    int cur = 0;
    while (spfa()) {
        cur += argument();
        if (cur + used * server_cost >= ans)
            return inf - 1;
    }
    return (flow == totle_flow) ? cur : inf;
}
/*}}}*/
inline bool bfs() {/*{{{*/
    memset(dist, 0, sizeof dist);
    qst = qed = 0;
    que[qed++] = source;
    //    que.push(source);
    dist[source] = inf;
    //    while (!que.empty()) {
    while (qst != qed) {
        //        int u = que.front();
        //        que.pop();
        int u = que[qst++];
        if (qst == maxn)
            qst = 0;
        if (u == sink)
            break;
        for (int i = g[u]; i; i = e[i].nxt) {
            if (i & 1)
                continue;
            if (e[i ^ 1].f > 0 && dist[e[i].v] == 0) {
                dist[e[i].v] = min(dist[u], e[i ^ 1].f);
                prev[e[i].v] = u;
                pree[e[i].v] = i ^ 1;
                //                que.push(e[i].v);
                que[qed++] = e[i].v;
                if (qed == maxn)
                    qed = 0;
            }
        }
    }
    //    while (!que.empty())
    //        que.pop();
    return dist[sink] > 0;
}/*}}}*/
inline string find() {/*{{{*/
    string ret = "";
    int u = prev[sink], cut = dist[sink];
    e[pree[sink]].f -= cut;
    e[pree[u]].f -= cut;
    out.clear();
    out.push_back(dist[sink]);
    out.push_back(u - node_num);
    while (u != source) {
        //each_flow[u] += e[pree[u] ^ 1].w * cut;
        u = prev[u];
        if (u == source)
            break;
        e[pree[u]].f -= cut;
        out.push_back(u);
    }
    reverse(out.begin(), out.end());
    for (auto i: out)
        ret += itoa(i) + " ";
    if (!ret.empty())
        ret[ret.size() - 1] = '\n';
    return ret;
}/*}}}*/
inline void update(string &res) {/*{{{*/
    res.clear();
    int cnt = 0;
    while (bfs()) {
        res += find();
        cnt ++;
    }
    res = itoa(cnt) + "\n\n" + res;
}/*}}}*/
inline void addsource() {/*{{{*/
    source_vec.clear();
    for (int i = 0; i < sink_num; i++)
        source_vec.push_back(father[i]);
}/*}}}*/
inline bool cmp(const int &a, const int &b) {/*{{{*/
    return out_flow[a] > out_flow[b];
}/*}}}*/
inline bool cmp1(const int &a, const int &b) {/*{{{*/
    return each_flow[a] > each_flow[b];
}/*}}}*/
inline bool cmp2(const int &a, const int &b) {/*{{{*/
    return each_flow[a] < each_flow[b];
}/*}}}*/
inline bool cmp3(const int &a, const int &b) {/*{{{*/
    return score[a] < score[b];
}/*}}}*/
inline int work() {/*{{{*/
    int totle = 0;
    for (auto i: source_vec)
        totle += out_flow[i];
    if (totle < totle_flow)
        return -1;
    build_edge();
    used = 0;
    memset(vis, 0, sizeof vis);
    memset(each_flow, 0, sizeof each_flow);
    int tmp = min_cost_flow();
    if (tmp == inf)
        return -1;
    tmp += used * server_cost;
    if (tmp < ans) {
        last_sink = used;
        ans = tmp;
        update(res);
        return 1;
    }
    return 0;
}/*}}}*/
inline void best_out() {/*{{{*/
    addsource();
    sort(source_vec.begin(), source_vec.end(), cmp);
    int cnt = source_vec.size();
    while (!source_vec.empty()) {
        int res = work();
#ifdef DEBUG
        cerr << TIME << " " << ans << " " << source_vec.size() << " " << endl;
#endif
        if (res == -1)
            break;
        if (res == 1)
            best_vec = source_vec;
        source_vec.pop_back();
        cnt--;
        if (TIME >= limit_best_time)
            break;
    }
}/*}}}*/
inline void insert(int num = 1) {/*{{{*/
    num = max(num, 5);
    sort(rest_vec.begin(), rest_vec.end(), cmp2);
    int random =  num >> 1, well = 2, good = num - random - well;
    good = min(num >> 2, 100), random = num - good;
    while (good) {
        if (rest_vec.size() == 0)
            return;
        if (each_flow[*rest_vec.rbegin()] == 0) {
            random += good;
            break;
        }
        source_vec.push_back(*rest_vec.rbegin());
        rest_vec.pop_back();
        good--;
    }
    sort(rest_vec.begin(), rest_vec.end(), cmp3);
    while (well) {
        if (rest_vec.size() == 0)
            return;
        int pick = log(max(rand(), 1)) / log_rand_max * rest_vec.size();
        swap(rest_vec[rest_vec.size() - 1], rest_vec[pick]);
        source_vec.push_back(*rest_vec.rbegin());
        rest_vec.pop_back();
        well--;
    }

    while (random--) {
        if (rest_vec.size() == 0)
            return;
        int x = rand() % rest_vec.size();
        swap(rest_vec[rest_vec.size() - 1], rest_vec[x]);
        source_vec.push_back(*rest_vec.rbegin());
        rest_vec.pop_back();
    }
}/*}}}*/
inline void pop_back(int num = 1) {/*{{{*/
    num = max(1, num);
    while (num-- && !source_vec.empty()) {
        rest_vec.push_back(*source_vec.rbegin());
        source_vec.pop_back();
    }
}/*}}}*/
inline void add_some_sink(int n) {/*{{{*/
    random_shuffle(rest_vec.begin(), rest_vec.end());
    int cnt = 0, m = rest_vec.size();
    for (int i = 0; i < m; i++) {
        if (is_near_sink[rest_vec[i]]) {
            source_vec.push_back(rest_vec[i]);
            swap(rest_vec[i], rest_vec[m - 1]);
            rest_vec.pop_back();
            m--;
            if (++cnt == n)
                break;
        }
    }       
}/*}}}*/
inline void work_iterator() {/*{{{*/
    source_vec.clear();

//    for (int i = 0; i < node_num; i++)
//        rest_vec.push_back(i);
    
//    random_shuffle(rest_vec.begin(), rest_vec.end());
    
//    sort(rest_vec.begin(), rest_vec.end(), cmp);
//    reverse(rest_vec.begin(), rest_vec.end());
//    for (int i = 0; i < sink_num; i++)
//        insert();

    sort(best_vec.begin(), best_vec.end());
    int id = 0;
    for (int i = 0; i < node_num; i++) {
        if (id < int(best_vec.size()) && i == best_vec[id]) {
            source_vec.push_back(i);
            id++;
        } else if (is_near_sink[i]) {
            rest_vec.push_back(i);   
        }
    }

    int cnt = 0;
    while (TIME < 88) {
        
        int res = work();
        if (res ==-1) {
            add_some_sink(source_vec.size() * 0.05);
            cnt++;
        } else {
            if (res == 0)
                cnt++;
            sort(source_vec.begin(), source_vec.end(), cmp1);
            pop_back(source_vec.size() * 0.05);
        }
        if (res == 1) {
            cnt = 0;
        } else {
            if (cnt == 10) {
                int x = source_vec.size();
                pop_back(x);
                add_some_sink(last_sink);
                cnt = 0;
            }
        }
//        if (double(source_vec.size()) / last_sink <= 0.8) {
//            add_some_sink(last_sink * 0.21);
//            cnt = 0;
//        }
#ifdef DEBUG
        cerr << TIME << " : " << ans << " " << source_vec.size() << " " << last_sink << " " << cnt << endl;
#endif
    }
}/*}}}*/
void deploy_server(char *topo[MAX_EDGE_NUM], int line_num,char *filename) {/*{{{*/
    srand(time(0) + clock() + my_favority_number);
    ans = inf;
    init(topo);
    for (int i = 0; i < sink_num; i++)
        sink_vec.push_back(father[i]);
#ifndef DEBUG
    limit_best_time = 15;
#else
    limit_best_time = 15;
#endif

    best_out();
    max_sink = ans / server_cost;
    
#ifdef DEBUG
    cerr << ans << " " << TIME << " " << server_cost * sink_num << " " << server_cost << "  "<< sink_num << endl;
#endif
    work_iterator();


    if (*res.rbegin() == '\n')
        res.pop_back();
    write_result(res.c_str(), filename);
}/*}}}*/
#undef TIME
#undef prev
