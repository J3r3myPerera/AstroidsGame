# AstroidsGame
A B specification of a simple version of the old Asteroids arcade game, using the B tools.
**State invariants**
1. The grid consists of 12 squares wide and 10 squares high and the spaceship should
always be inside of these boundaries. If the spaceship moves out of these bounds then
an error will be created as in the operations.
2. The spaceship's current position will always be inside of the grid's boundaries and
contain the X and Y coordinates of the grid as the location.
3. 4. The variables defined will always carry non negative positive values.
The current gamestate will always be the value of the defined set of GAMESTATE and the
spaceship direction will always be the values defined in the DIRECTIONS set as defined in
the SETS part of the machine.
5. The Asteroids need to be placed inside of the grid boundaries. There cannot be small
and large asteroids in the same grid position.
6. Asteroids(large and small), empty space, homebase and starbase are all subsets or
elements of the Grid. Which means that none of them can exist outside of the grid
boundaries.
7. The Spaceship will always start at the Homebase and face right. The spaceship will have
the initial power value. The moves, number of collisions and the number of destroyed
asteroids will be set to zero.
8. The initial asteroid positions will be as predetermined and the gamestate will be set to
ONGOING.
