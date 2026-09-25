## S - Two doors

Score : $8$ points

### Problem Statement

You are given an $N \times N$ grid. Let $(i,j)$ denote the cell in the $i$\-th row from the top and the $j$\-th column from the left.

The state between adjacent cells (sharing an edge) is represented by a character $c$:

-   If $c = $ `.`, there is nothing between the cells, and you can pass freely.
-   If $c = $ `D`, there is a door, and you can pass freely.
-   If $c = $ `A`, there is a special door called $A$, and you can pass freely.
-   If $c = $ `B`, there is a special door called $B$, and you can pass freely.
-   If $c = $ `#`, there is a wall, and you cannot pass.

Here, there is exactly one door $A$ and one door $B$ in the grid.

The states between adjacent cells are given by strings $S_1, S_2, \dots, S_{N-1}$ and $T_1, T_2, \dots, T_N$:

-   For $1 \leq i \leq N-1$, $1 \leq j \leq N$, the state between $(i,j)$ and $(i+1,j)$ is $S_{i,j}$.
-   For $1 \leq i \leq N$, $1 \leq j \leq N-1$, the state between $(i,j)$ and $(i,j+1)$ is $T_{i,j}$.

A grid is called a **good state** if you can start from $(1,1)$ and reach $(N,N)$ by moving up, down, left, or right without passing through walls.

You will block some of the doors (except $A$ and $B$), making them impassable, so that the following conditions are satisfied:

-   The grid is in a good state.
-   Even if you additionally block exactly one of $A$ or $B$, the grid is still in a good state.
-   If you additionally block both $A$ and $B$, the grid is no longer in a good state.

Is it possible to satisfy these conditions? If it is possible, find the minimum number of doors you need to block.

You are given $T$ test cases. Solve each of them.

### Constraints

-   $1 \leq T \leq 10^5$
-   $2 \leq N \leq 40$
-   Each $S_i$ is a string of length $N$ consisting of `.`, `D`, `A`, `B`, `#`
-   Each $T_i$ is a string of length $N-1$ consisting of `.`, `D`, `A`, `B`, `#`
-   `A` and `B` each appear exactly once among all $S_{i,j}$ and $T_{i,j}$
-   The sum of $N^2$ over all test cases is at most $2 \times 10^5$
-   The sum of $N^4$ over all test cases is at most $40^4$

* * *

### Input

The input is given from standard input in the following format:

```
$T$
$\mathrm{case}_1$
$\mathrm{case}_2$
$\vdots$
$\mathrm{case}_T$
```

Each test case is given in the following format:

```
$N$
$S_1$
$S_2$
$\vdots$
$S_{N-1}$
$T_1$
$T_2$
$\vdots$
$T_N$
```

### Output

Print $T$ lines. On the $i$\-th line, output the answer for the $i$\-th test case.  
For each test case, if it is possible to satisfy the conditions, output the minimum number of doors that need to be blocked; otherwise, output `-1`.

* * *

### Sample Input 1

```
6
2
.A
.
B
2
.A
#
B
3
#D.
#BD
.A
.#
..
4
DDBD
..#D
#D.D
#DD
#DD
.A.
#.#
4
D.#D
DD#.
D.B.
#D.
.#D
...
.DA
9
DDD.D#DDD
DDDADDDDD
DD.DDDDDD
DDDD#.DDD
DD#DDDD.#
DDDDD#.#D
DD.#..DDD
DDDDD#D.D
DDD...DD
D#.D#D#D
D#DD#D.#
DDD#DD##
BDDD.D#D
DD#DDDDD
DDDDD#DD
DDD#DDDD
##DDD.#D
```

### Sample Output 1

```
0
-1
0
3
-1
7
```

For example, in the first test case, the conditions are already satisfied.
