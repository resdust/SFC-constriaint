from z3 import *
import time
import random

# define global variables
N = 100
K = [500 for i in range(N)]
F = 1
Lamb = [0 for i in range(F)]
L = 8 # longest Length
T = 8 # QoS
# S = int(random.random()*N)
# D = int(random.random()*N)
S = [50]
D = [0]

# load topology
def load_edges(file):
    edges = {} 
    B = {}
    topo = [] # topo[i] concludes the nodes connected to node i
    with open(file) as f:
        datas = f.readlines()
  
    for d in datas:
        d = d.split()
        d = [int(x) for x in d]
        i,j,b = d[0],d[1],d[2]
        if i in edges:
            edges[i].append([j,b])
        else:
            edges[i] = [[j,b]]

    i = 0
    keys = list(edges.keys())
    keys.sort()
    for key in keys:
        while(i!= key):
            i = i+1
            topo.append([])
        topo.append([j[0] for j in edges[key]])
        B[key] = [j[1] for j in edges[key]]
        i = i+1

    print('===Loaded topology with '+str(len(topo))+' nodes===')
    return topo,B

# incoming nodes of C[i][j]
def nodes_out(i,j,C):
    nodes = []
    for k in edges[j]:
        nodes.append(C[i][k])
    return nodes

# outcoming nodes of C[i][j]
def nodes_in(i,j,C):
    nodes = []
    for node in range(len(edges)):
        for e in edges[node]:
            if e==j:
                nodes.append(C[i][node])
                break
    return nodes

# calculate the distance of every reachable node for Ci(src)
# dijkstra算法实现，有向图和路由源点作为函数的输入，最短路径最为输出
def dijkstra(src):
    graph = []
    # 补全有向拓扑图graph[i][j]为i到j的直接距离，不可达为inf，可达为1
    for i in range(len(edges)):
        nodes = edges[i]
        line = [float('inf')]*N
        for n in nodes:
            line[n] = 1
        graph.append(line)
    nodes = [i for i in range(len(graph))]  # 获取图中所有节点
    visited=[]  # 表示已经路由到最短路径的节点集合
    if src in nodes:
        visited.append(src)
        nodes.remove(src)
    else:
        print ('source node out of range!')
        return None
    distance={src:0}  # 记录源节点到各个节点的距离
    for i in nodes:
        distance[i]=graph[src][i]  # 初始化
    # path={src:{src:[]}}  # 记录源节点到每个节点的路径
    k=pre=src
    while nodes:
        mid_distance=float('inf')
        for v in visited:
            for n in nodes:
                new_distance = distance[v]+graph[v][n]
                if new_distance < mid_distance:
                    mid_distance=new_distance
                    graph[src][n]=new_distance  # 进行距离更新
                    k=n
                    pre=v
        distance[k]=mid_distance  # 最短路径
        # path[src][k]=path[src][pre]+[k]
        # 更新两个节点集合
        if k in visited: # 没有新的可达节点
            break
        visited.append(k)
        if k in nodes:
            nodes.remove(k)
    return distance

def gen_flow():
    constrains = []
    solvers = []
    # generate nodes (components) in z3 variables
    C = [[Int('c_'+str(i)) for i in range(N)] for j in range(F)]

    for i in range(F):
        solver = Solver()
        dis = dijkstra(D[i])
        constrains.append(C[i][S[i]] == 1)
        constrains.append(C[i][D[i]] == 1)

        for j in range(N):
            Sigma = Sum(C[i])*Lamb[i]
            outs = nodes_out(i,j,C)
            ins = nodes_in(i,j,C)
            nodes = outs + ins
            cons = []
            inter = []
            constrains.append(Or(C[i][j]==1, C[i][j]==0))

            if (j != S[i] and j != D[i]): 
                # Rechability constraint
                for n in nodes:
                    k = int(n.decl().name().split('_')[1])
                    if dis[k]<dis[j]:
                        inter.append(And(C[i][j]==1,C[i][k]==1))          
                if inter != []:
                    cons = Or(inter)
                    constrains.append(Implies(C[i][j]==1, cons))
                # Incoming == Outcomint
                constrains.append(Sum(ins)==Sum(outs))
                # Loop constraint
                constrains.append(Implies(C[i][j]==1,Sum(nodes)<=2))
            elif (j == S[i]): # Source
                constrains.append(Sum(outs)==1)
                constrains.append(Sum(ins)==0)
            else: # Destination
                constrains.append(Sum(ins)==1)
                constrains.append(Sum(outs)==0)
            
            # Load Satisfaction constraint
            constrains.append(Implies(C[i][j]==1, Sigma<=K[j]-Lamb[i]))
            # Node stress constraint
            constrains.append(Sigma<=K[j]-T)

        # QoS constraint -> Length constraint
        constrains.append(Sum(C[i])<=T)
        # Pair Mapping constraint
        constrains.append(Sum(C[i])>1)

        solver.add(constrains)
        print(solver.check())
        solvers.append(solver)
    return solvers

def get_solution(solvers):
    for i in range(F):
        res_file.write('===Flow %d===\n' %(i))
        for i in range(len(solvers)):
            solver = solvers[i]
            if solver.check()!=sat:
                print('No solution!')
                res_file.write('No solution!')
                exit(0)
            
            routes = []
            count = 0
            while(solver.check()==sat):
                print('Solution %d:' %(count+1))
                
                count = count + 1
                m = solver.model()
                route = []
                cons = []
                for d in m.decls():
                    if m[d]==1 and d.name()[0]=='c':
                        print("{}={}".format(d.name(),m[d]),end=', ')
                        route.append(d.name())
                        cons.append(d()==0)
                routes.append(route)
                solver.append(Or(cons))
                plot_routes(route,count,i)
                print('======')
    return routes

def plot_routes(route,count,i):
    flow = {}
    route = [c.split('_')[1] for c in route]
    for c in route:
        for j in edges[int(c)]:
            if str(j) in route:
                flow[c] = j
    
    if str(S[i]) in flow:
        second = flow[str(S[i])]
    else:
        second = None

    # trace the flow
    res_file.write('Solution %d:\n' %(count+1))
    print(S[i],end='->')
    res_file.write(str(S[i])+'->')
    while second in flow:
        print(second,end='->')
        res_file.write(second+'->')
        second = flow[second]

    if second == str(D[i]):
        print(D[i])
        res_file.write(str(D[i])+'\n')
        print('correct solution!')
    else:
        print(second)
        print('Not reaching destination, wrong solution!')

def main():
    times = []
    times.append(time.time())
    
    print('Source node: ',S)
    print('Destination node: ',D)
    res_file.write('Source node: '+str(S)+'\n')
    res_file.write('Destination node: '+str(D)+'\n')
    times.append(time.time())

    solvers = gen_flow()
    times.append(time.time())

    print('===final solution===')
    print('adding constraints time:',times[-1]-times[0])
    routes = get_solution(solvers)
    times.append(time.time())
    print('total time used:',times[-1]-times[0])

res_file = open('RRM_result.txt','w',encoding='utf-8')
edges,B = load_edges('network-brand.txt')
main()
res_file.close()