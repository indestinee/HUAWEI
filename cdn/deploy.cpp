#include "deploy.h"
#include <cstdio>
#include <cstring>
#include <algorithm>
#include <queue>
#include <string>
#include <iostream>
using namespace std;
#define prev prevDSJAIOIOWD
#define TIME (double(clock())/double(CLOCKS_PER_SEC))
const int maxm = 210000, inf = 0x63636363, maxn = 4024, my_favority_number = 91203;
int node_num, edge_num, sink_num, server_cost, totle_flow, ans, source, sink, nume, flow, used, limit_del_some_sink, limit_sink_random, limit_random_high_out_flow, limit_random, st[maxm], ed[maxm], limit[maxm], cost[maxm], sink_node[maxn], father[maxn], need[maxn], g[maxn], dist[maxn], prev[maxn], pree[maxn], vis[maxn], out_flow[maxn], id[maxn], que[maxn], qst, qed, limit_best_time;
string res;
vector<int> random_pick, out, source_vec;
bool inque[maxn];
char buff[1 << 20];
inline void init(char *topo[MAX_EDGE_NUM]) {/*{{{*/
	sscanf(topo[0], "%d%d%d", &node_num, &edge_num, &sink_num);
    sscanf(topo[2], "%d", &server_cost);
    for (int i = 0; i < edge_num; i++) {
        sscanf(topo[i + 4], "%d%d%d%d", &st[i], &ed[i], &limit[i], &cost[i]);
        out_flow[st[i]] += limit[i];
        out_flow[ed[i]] += limit[i];
    }
    for (int i = 0; i < sink_num; i++) {
        sscanf(topo[i + 5 + edge_num], "%d%d%d", &sink_node[i], &father[i], &need[i]);
        totle_flow += need[i];
        out_flow[father[i]] += need[i];
    }
}/*}}}*/
class edge{/*{{{*/
public:
    edge () { }
    edge (const int &v, const int &f, const int &w, const int &nxt): v(v), f(f), w(w), nxt(nxt) { }
    int v, f, w, nxt;
} e[maxm];/*}}}*/
inline void addedge(const int &u, const int &v, const int &c, const int &w) {/*{{{*/
    if (w > ans || w > server_cost)
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
            return inf;
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
inline string find() {/*{{{*/
    string ret = "";
    int u = prev[sink], cut = dist[sink];
    e[pree[sink]].f -= cut;
    e[pree[u]].f -= cut;
    out.clear();
    out.push_back(dist[sink]);
    out.push_back(u - node_num);
    while (u != source) {
        u = prev[u];
        e[pree[u]].f -= cut;
        if (u != source)
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
inline void random(const int &x) {/*{{{*/
    for (int i = 0; i < x; i++) {
        if (i == node_num)
            continue;
        int x = rand() % (node_num - i) + i;
        swap(random_pick[i], random_pick[x]);
    }
}/*}}}*/
inline void rand_add_source(const int &m) {/*{{{*/
    random(m);
    source_vec.clear();
    for (int i = 0; i < m; i++)
        source_vec.push_back(random_pick[i]);
}/*}}}*/
inline bool work(int flag = 0) {/*{{{*/
    if (flag) {
        random(flag);
        rand_add_source(flag);
    }
    int totle = 0;
    for (auto i: source_vec)
        totle += out_flow[i];
    if (totle < totle_flow)
        return false;
    build_edge();
    used = 0;
    memset(vis, 0, sizeof vis);
    int tmp = min_cost_flow();
    tmp += used * server_cost;
    if (tmp < ans) {
        ans = tmp;
        update(res);
        return true;
    }
    return false;
}/*}}}*/
inline void sink_random() {/*{{{*/
    addsource();
    random_shuffle(source_vec.begin(), source_vec.end());
    int cnt = 0;
    while (!source_vec.empty()) {
        source_vec.pop_back();
        if (TIME > limit_sink_random)
            break;
        if (!work()) {
            if (++cnt == 3)
                break;
        } else {
            cnt = 0;
        }
    }
}/*}}}*/
inline void random_addsource() {/*{{{*/
    for (int i = max(0, sink_num - 10); i <= min(node_num, sink_num + 10); i++) {
        if (TIME > limit_random)
            break;
        work(i);
    }
}/*}}}*/
inline int cmp(const int &a, const int &b) {/*{{{*/
    return out_flow[a] > out_flow[b];
}/*}}}*/
inline void random_high_out_flow() {/*{{{*/
    for (int i = 0; i < node_num; i++)
        id[i] = i;
    sort(id, id + node_num, cmp);
    source_vec.clear();
    int sum = 0;
    for (int i = 0; i < node_num; i++)  {
        source_vec.push_back(id[i]);
        sum += out_flow[id[i]];
        if (sum < totle_flow)
            continue;
        work();
        //cerr << ans << endl;
        if (TIME > limit_random_high_out_flow)
            break;
    }
}/*}}}*/
inline void del_some_sink() {/*{{{*/
    for (int j = 0; j < sink_num; j++) {
        if (TIME > limit_del_some_sink)
            return;
        source_vec.clear();
        for (int i = 0; i < sink_num; i++)
            if (i != j)
                source_vec.push_back(father[i]);
        work();
    }
    for (int j = 0; j < sink_num; j++) {
        for (int k = j + 1; k < sink_num; k++) {
            if (TIME > limit_del_some_sink)
                return;
            source_vec.clear();
            for (int i = 0; i < sink_num; i++)
                if (i != j && i != k)
                    source_vec.push_back(father[i]);
            work();
        }
    }
}/*}}}*/
inline void best_out() {
    addsource();
    sort(source_vec.begin(), source_vec.end(), cmp);
    while (!source_vec.empty()) {
        work();
        source_vec.pop_back();
        if (TIME >= limit_best_time)
            break;
    }
}
//#define DEBUG
void deploy_server(char *topo[MAX_EDGE_NUM], int line_num,char *filename) {/*{{{*/
    ans = inf;
    srand(time(0) + clock() + my_favority_number);
    init(topo);
    for (int i = 0; i < node_num; i++)
        random_pick.push_back(i);
    random_shuffle(random_pick.begin(), random_pick.end());
#ifndef DEBUG
    limit_best_time = 30;
    limit_random_high_out_flow = 45;
    limit_del_some_sink = 60;
    limit_sink_random = 75;
    limit_random = 88;
#else
    limit_best_time = 10;
    limit_random_high_out_flow = 13;
    limit_del_some_sink = 15;
    limit_sink_random = 17;
    limit_random = 19;
#endif
    /*  choose all sink node    */
    best_out();
#ifdef DEBUG
    cerr << ans << " " << TIME << endl;
#endif

    /*  choose high_out_flow node   */
    random_high_out_flow();
#ifdef DEBUG
    cerr << ans << " " << TIME << endl;
#endif

    /*  del some sink node  */
    while (true && TIME <= limit_del_some_sink)
        del_some_sink();
#ifdef DEBUG
    cerr << ans << " " << TIME << endl;
#endif
//        cerr << ans << " " << TIME << endl;

    while (true && TIME <= limit_sink_random)
        sink_random();
#ifdef DEBUG
    cerr << ans << " " << TIME << endl;
#endif

    /*  random choose   */
    while (true && TIME <= limit_random)
        random_addsource();
#ifdef DEBUG
    cerr << ans << " " << TIME << endl;
#endif


    if (*res.rbegin() == '\n')
        res.pop_back();
    write_result(res.c_str(), filename);
}/*}}}*/
#undef TIME
#undef prev
