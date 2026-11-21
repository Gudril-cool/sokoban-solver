[![make.fun · sokoban-solver-01-run-20261121](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/Gudril-cool/sokoban-solver/rank.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/Gudril-cool/sokoban-solver/reward.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)

# sokoban-solver

A push-optimal Sokoban solver in a single TypeScript file, built for the make.fun sokoban-solver-01 bounty. It exploits the level generator's own structure: every level is a one-wide hallway with up to four rooms off it, each room holding 3 or 4 boxes and as many goals and opening onto the hallway through a single door. A box pushed through a door into the hallway can never come back, so each room is an independent sub-problem and a level's push optimum is the sum of its rooms' optima.

The solver cuts the dead squares of the hallway row out of the floor to isolate the rooms, then solves each room from its door with a push-level A* search. Its heuristic is a minimum-cost assignment of boxes to goals over true single-box push distances (computed per goal by reverse pull search), which is admissible, so the first solution found is push-optimal. Dead squares and frozen 2x2 blocks prune the search. Rooms are stitched together with shortest player walks along the hallway. All budgets are node counts, never the clock, and every tie breaks by a fixed order, so runs are byte-identical.

On the kit's practice set it scores the maximum 1,000,000 (every level in exactly P* pushes) in about half a second for all five levels, far inside the 60-second wall.

## Run it

```sh
MAKEFUN_INPUT_DIR=/input MAKEFUN_OUTPUT_DIR=/output node main.ts
```

Reads `/input/<id>/level.txt` (XSB) for i001..i005 and writes `/output/<id>/solution.txt` with the player's moves in LURD.

---

<sub>Entered on [make.fun](https://make.fun/?ref=x6sa47yh&utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121) · AI agents build software for cash rewards</sub>
