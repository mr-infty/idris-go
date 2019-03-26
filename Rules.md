# Logical Rules (based on the ones by J. Tromp)

0. A *board* is a *set* `G` together with a symmetric, irreflexive relation `a`.
   The elements of `G` are called *points*. Two points `P,Q` $\in$ `G` are called
   *adjacent* iff `PaQ`.

1. *pre-Go* is played on a board `G` by players `Black` and `White`. A game of
   *pre-Go* is a game of *Go* iff the board `G` together with its adjacency
   relation is isomorphic to a board of the form

   $$\texttt{G} = \{0, \ldots, n-1\}^2,\quad (i,j)a(i',j') \Leftrightarrow |i-i'| + |j-j'| = 1$$

2. A *coloring* of a board `G` is a map assigning to each point one of three
   colors, `black`, `white` or `empty`.

3. A *path* is a finite non-empty sequence of pairwise adjacent or equal
   points. A path is called *monochrome* (with respect to a given coloring) if
   all its points have the same color. Two points `P` and `Q` are said to lie
   in the same group with respect to a given coloring iff there exists
   a monochrome path starting in `P` and ending in `Q`.

4. A point `P` is said to *reach* a colour `C` iff `P` lies in the same group as
   a point `Q` that is adjacent to a point of colour `C`.

5. Given a coloring $\gamma$ and a color `c`, a coloring $\gamma'$ is said to
   be obtained from $\gamma$ by *clearing the color `c`* iff

   $$\gamma'(\texttt{P}) = \texttt{empty}$$

   for all `P` with $\gamma(\texttt{P}) = \texttt{c}$ that don't reach empty with respect to $\gamma$ and

   $$\gamma'(\texttt{P}) = \gamma(\texttt{P})$$

   for all other `P`.

6. A *board situation* consists of:

    a) a coloring
    b) the number `N_white` of captured white stones
    c) the number `N_black` of captured black stones
    d) the player `P`$\in\{$`Black`, `White`$\}$ whose turn it is

7. Given a board situation `S`, a *potentially valid move* is either

    a) `Pass`
    b) `Put P`, where the point `P` is colored `empty` in the situation `S`

6. A *game* is a finite linear directed graph whose nodes are labelled with
   board situtations and whose edges are labelled by potentially valid moves
   that

    a) starts with the situation `S_start` defined by

           S_start.col(P) = empty
           S_start.N_white = 0
           S_start.N_black = 0
           S_start.Player = Black

    and such that for each edge labelled `M`, starting in `S1` and ending in
    `S2`, it holds that

    b) `S2.Player` = `opp(S1.Player)` (*opponent*)

    c. `S2.coloring` does not appear in the list of *previous* colorings
    and moroever one of the following holds

    d) `M` = `Pass`, `S2.coloring` = `S1.coloring`, and the previous two moves
    weren't passes

    e) `M` = `Put P`, `S2` is obtained by first coloring `P` with the colour
   `col(S1.Player)`, then clearing `col(opp(S1.Player))`, then clearing
   `col(S1.Player))`, and finally adding the numbers of points of colour
   `black` and `white` that were emptied during this process to `N_white` and
   `N_black`
   
7. A game has *ended* iff it ends in two passes.

8. The score of player `P` in situation `S` is equal to the sum of the number
   of points colored `col(P)` plus `N_opp(col(P))` plus the number of empty
   points that reach `col(P)` but don't reach `col(opp(P))`.

9. A game that has ended is won by player `P` iff his score is bigger than the
   score of his opponent in the final situation.
