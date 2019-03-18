# Logical Rules (based on the ones by J. Tromp)

1. *Go* is played on a `n`x`n` grid `G` of points, by players `Black` and `White`.

2. Each *point* `P`$\in$`G` is either *colored* `black`, `white` or `empty`.

3. Two points `P` and `Q` are said to lie in the same *group* if there is
   a *path* (list of length $2 <= l < \infty$ of pairwise *adjacent*
   points) starting in `P` and ending in `Q`, consisting of points of the same
   color.

4. A point `P` is said to *reach* a colour `C` if `P` lies in the same group as
   a point `Q` that is adjacent to a point of colour `C`.

5. *Clearing* a color means emptying all points of that color that don't reach
   `empty`.

6. A *board situation* consists of:
    a) a coloring of each point of the board
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
   
7. A game has *ended* if it ends in two passes.

8. The score of player `P` in situation `S` is equal to the sum of the number
   of points colored `col(P)` plus `N_opp(col(P))` plus the number of empty
   points that reach `col(P)` but don't reach `col(opp(P))`.

9. A game that has ended is won by player `P` if his score is bigger than the
   score of his opponent in the final situation.
