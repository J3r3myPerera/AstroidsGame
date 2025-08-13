MACHINE ASTEROIDS_GAME
SETS
    REPORT = {Success, Error_OutOfBounds, Low_Power, Game_Over, Returned_to_Starbase, Returned_to_Homebase, Move_Success, Hit_Astroid, Astroid_Destroyed, Miss};
    GAMESTATE = {WON, LOST, ONGOING};
    TURN= {Clockwise, AntiClockwise};
    DIRECTIONS = {Up, Down, Left, Right}
DEFINITIONS
    //if the next moving postion has an asteroid present
    isSpaceShipAstroidCollision( xx, yy ) == ((xx |-> yy) : largeAstroids \/ smallAstroids);
    //is there enough power to move to another grod position
    isPowerEnoughToMove(power, ramainingPower) == (power >= ramainingPower);
    //is the location within the grid positions
    isWithinGrid(xx, yy) == (xx |-> yy : Grid);
    //has the spaceship returned to the Starbase
    isReturnedToStarBase == (spaceshipXPos |-> spaceshipYPos = Starbase);
    //either small or large asteroid
    isSmallAstroid(xx, yy) == (xx |-> yy : smallAstroids);
     //either small or large asteroid
    isLargeAstroid(xx,yy) == (xx |-> yy : largeAstroids)
CONSTANTS
    Grid, GridX, GridY, Homebase, Starbase,  InitialPower, TurnPower, MovePower, ShootPower, LargeAstroids, SmallAstroids, EmptySpace, Astroids
PROPERTIES
    //Grid length and height as mentioned in the specification
    GridX = 1..12 &
    GridY = 1..10 &
    Grid = GridX * GridY &
    //Asteroid are inside of the grid and the locations of the asteroids as mentioned in the specification
    Astroids <: Grid &
    LargeAstroids = { (2 |-> 1), (3 |-> 7), (5 |-> 4), (6 |-> 2), (6 |-> 3), (6 |-> 7), (6 |-> 8), (8 |-> 1), (8 |-> 5), (8 |-> 9), (10 |-> 7), (10 |-> 9), (11 |-> 8)} &
    SmallAstroids = {(1 |-> 6), (2 |-> 4), (2 |-> 7), (3 |-> 4), (4 |-> 6), (4 |-> 7), (4 |-> 9), (5 |-> 6), (6 |-> 5), (7 |-> 5), (8 |-> 4), (9 |-> 6), (10 |-> 2), (10 |-> 5), (11 |-> 5), (12 |-> 4), (12 |-> 9)} &
    //A large and a small asteroid cannot be present in the same grid location
    LargeAstroids /\ SmallAstroids = {} &
    Astroids = (LargeAstroids \/ SmallAstroids) &
    //properties of emptyspace
    EmptySpace <: Grid &
    EmptySpace /\ Astroids = {} &
    EmptySpace \/ Astroids = Grid &
    //Homebase and Starbase are in the empty space and the locations as mentioned in the specification
    Homebase : EmptySpace &
    Starbase : EmptySpace &
    Homebase = 1 |-> 1 &
    Starbase = 8 |-> 7 &
    //constant values as mentioned in the specification for operations
    InitialPower = 100 &
    TurnPower = 3  &
    MovePower = 5 &
    ShootPower = 20
VARIABLES
    spaceshipXPos, spaceshipYPos, spaceshipCurrentPos, spaceshipPower, noOfCollitions, movesMade, spaceshipDirection, noOfAstroidsDestroyed, currentGamestate, largeAstroids, smallAstroids
INVARIANT
    //Spaceship locations
    spaceshipXPos : GridX &
    spaceshipYPos : GridY &
    //Natural values for the variables holding the values
    spaceshipPower : NATURAL &
    noOfCollitions : NATURAL &
    movesMade : NATURAL &
    noOfAstroidsDestroyed : NATURAL &
    //Location of the spaceship at the current time
    spaceshipCurrentPos : Grid &
    //Variables that contain values belonging to the above mentioned sets
    currentGamestate : GAMESTATE &
    spaceshipDirection : DIRECTIONS &
    largeAstroids : POW(Grid) &
    smallAstroids : POW(Grid)
INITIALISATION
    //SpaceShip is at the homebase
    spaceshipXPos := 1 ||
    spaceshipYPos := 1 ||
    //Spaceship starts with the initial power as mentioned above
    spaceshipPower := InitialPower ||
    //Initial values are set to 0 at the start
    noOfCollitions := 0 ||
    movesMade := 0 ||
    noOfAstroidsDestroyed := 0 ||
    //SpaceShip current position is at the homebase
    spaceshipCurrentPos := Homebase ||
    //Game is ongoing
    currentGamestate := ONGOING ||
    //SpaceShip current heading is righ as mentioned in the specification
    spaceshipDirection := Right ||
    //Above constant values are assiged to the variable sets created
    largeAstroids := LargeAstroids ||
    smallAstroids := SmallAstroids
OPERATIONS
    
//Operation for the start of a new game
report <-- NewGame(power) = 
PRE
    power : NATURAL &
    power > 0
THEN
    //Setting the initial values to the variables as the game is a new game
    spaceshipCurrentPos := Homebase||
    spaceshipDirection := Right ||
    spaceshipPower := power ||
    currentGamestate := ONGOING ||
    movesMade := 0 ||
    noOfAstroidsDestroyed := 0 ||
    report := Returned_to_Homebase ||
    largeAstroids := LargeAstroids ||
    smallAstroids := SmallAstroids
END;

//Operation for the turning of the spaceship
report <-- Turn(side) = 
PRE
    //Turn can happen only for either Clockwise or Anticlockwise
    side : TURN &
    currentGamestate = ONGOING 
THEN
    //Turn can happen only if the power of the spaceship is above the turning power neeeded
    IF spaceshipPower >=3 THEN
        IF spaceshipDirection = Right & side = Clockwise THEN
            spaceshipDirection := Down ||
            spaceshipPower := spaceshipPower - TurnPower ||
            report := Success
        ELSIF spaceshipDirection = Right & side = AntiClockwise THEN
            spaceshipDirection := Up ||
            spaceshipPower := spaceshipPower - TurnPower ||
            report := Success
        ELSIF spaceshipDirection = Left & side = AntiClockwise THEN
            spaceshipDirection := Down ||
            spaceshipPower := spaceshipPower - TurnPower ||
            report := Success
        ELSIF spaceshipDirection = Left & side = Clockwise THEN
            spaceshipDirection := Up ||
            spaceshipPower := spaceshipPower - TurnPower ||
            report := Success
        ELSIF spaceshipDirection = Up & side = Clockwise THEN
            spaceshipDirection := Right ||
            spaceshipPower := spaceshipPower - TurnPower ||
            report := Success
         ELSIF spaceshipDirection = Up & side = AntiClockwise THEN
            spaceshipDirection := Left ||
            spaceshipPower := spaceshipPower - TurnPower ||
            report := Success
         ELSIF spaceshipDirection = Down & side = Clockwise THEN
            spaceshipDirection := Left ||
            spaceshipPower := spaceshipPower - TurnPower ||
            report := Success
         ELSIF spaceshipDirection = Down & side = AntiClockwise THEN
            spaceshipDirection := Right ||
            spaceshipPower := spaceshipPower - TurnPower ||
            report := Success
          END
    ELSE
        //Having low power means that the spaceship would not be able to move as well the game is lost
        report := Low_Power ||
        currentGamestate := LOST
    END
END;

//Operation to move the spaceship from one position to another
report <-- Move =
PRE
    currentGamestate = ONGOING
THEN
    IF (spaceshipDirection = Up) THEN
        //Check if there is enough power to move
        IF isPowerEnoughToMove(spaceshipPower, MovePower) THEN
            //Check if the location is within the Grid positions
            IF isWithinGrid(spaceshipXPos, spaceshipYPos + 1) THEN
                //Check if returned to starbase
                IF not(isReturnedToStarBase) THEN
                    //Check if there is an asteroid in the next Grid postion
                    IF not(isSpaceShipAstroidCollision(spaceshipXPos, spaceshipYPos + 1)) THEN
                        spaceshipYPos := spaceshipYPos + 1 ||
                        spaceshipCurrentPos := (spaceshipXPos |-> spaceshipYPos + 1) ||
                        spaceshipPower := spaceshipPower - MovePower ||
                        movesMade := movesMade + 1||
                        report := Move_Success
                    ELSE
                        //If asteroid collition then power set to zero and game lost due to no power to move
                        spaceshipPower := 0 ||
                        noOfCollitions := noOfCollitions + 1 ||
                        report := Hit_Astroid ||
                        currentGamestate := LOST
                    END
                ELSE
                    //If returned to starbase then the game is won
                    currentGamestate := WON ||
                    report := Game_Over
                END
            ELSE
                //Cannot move out of the Grid positions
                report := Error_OutOfBounds
            END
        ELSE
            //If no power to move then the game is lost
            currentGamestate := LOST ||
            report := Low_Power
        END
ELSIF (spaceshipDirection = Down) THEN
    //Check if there is enough power to move
    IF isPowerEnoughToMove(spaceshipPower, MovePower) THEN
        //Check if the location is within the Grid positions
            IF isWithinGrid(spaceshipXPos, spaceshipYPos - 1) THEN
                //Check if returned to starbase
                IF not(isReturnedToStarBase) THEN 
                    //Check if there is an asteroid in the next Grid postion
                    IF not(isSpaceShipAstroidCollision(spaceshipXPos, spaceshipYPos - 1)) THEN
                        spaceshipYPos := spaceshipYPos - 1 ||
                        spaceshipCurrentPos := (spaceshipXPos |-> spaceshipYPos - 1) ||
                        spaceshipPower := spaceshipPower - MovePower ||
                        movesMade := movesMade + 1 ||
                        report := Move_Success
                    ELSE
                        //If asteroid collition then power set to zero and game lost due to no power to move
                        spaceshipPower := 0 ||
                        noOfCollitions := noOfCollitions + 1 ||
                        report := Hit_Astroid ||
                        currentGamestate := LOST
                    END
               ELSE
               //If returned to starbase then the game is won
               currentGamestate := WON ||
               report := Game_Over
           END
            ELSE
                 //Cannot move out of the Grid positions
                report := Error_OutOfBounds
            END
        ELSE
            //If no power to move then the game is lost
            currentGamestate := LOST ||
            report := Low_Power
        END
ELSIF (spaceshipDirection = Right) THEN
    //Check if there is enough power to move
    IF isPowerEnoughToMove(spaceshipPower, MovePower) THEN
        //Check if the location is within the Grid positions
            IF isWithinGrid(spaceshipXPos + 1, spaceshipYPos) THEN
                //Check if returned to starbase
                IF not(isReturnedToStarBase) THEN 
                    //Check if there is an asteroid in the next Grid postion
                    IF not(isSpaceShipAstroidCollision(spaceshipXPos + 1, spaceshipYPos)) THEN
                        spaceshipXPos := spaceshipXPos + 1 ||
                        spaceshipCurrentPos := (spaceshipXPos + 1 |-> spaceshipYPos) ||
                        spaceshipPower := spaceshipPower - MovePower ||
                        movesMade := movesMade + 1 ||
                        report := Move_Success
                    ELSE
                        //If asteroid collition then power set to zero and game lost due to no power to move
                        spaceshipPower := 0 ||
                        noOfCollitions := noOfCollitions + 1 ||
                        report := Hit_Astroid ||
                        currentGamestate := LOST
                    END
                ELSE
                    //If returned to starbase then the game is won
                    currentGamestate := WON ||
                    report := Game_Over
                 END
            ELSE
                 //Cannot move out of the Grid positions
                report := Error_OutOfBounds
            END
        ELSE
            //If no power to move then the game is lost
            currentGamestate := LOST ||
            report := Low_Power
        END
ELSIF (spaceshipDirection = Left) THEN
    //Check if there is enough power to move
    IF isPowerEnoughToMove(spaceshipPower, MovePower) THEN
        //Check if the location is within the Grid positions
            IF isWithinGrid(spaceshipXPos - 1, spaceshipYPos) THEN
                //Check if returned to starbase
                IF not(isReturnedToStarBase) THEN 
                    //Check if there is an asteroid in the next Grid postion
                    IF not(isSpaceShipAstroidCollision(spaceshipXPos - 1, spaceshipYPos)) THEN
                        spaceshipXPos := spaceshipXPos - 1 ||
                        spaceshipCurrentPos := (spaceshipXPos - 1 |-> spaceshipYPos) ||
                        spaceshipPower := spaceshipPower - MovePower ||
                        movesMade := movesMade + 1 ||
                        report := Move_Success
                    ELSE
                        //If asteroid collition then power set to zero and game lost due to no power to move
                        spaceshipPower := 0 ||
                        noOfCollitions := noOfCollitions + 1 ||
                        report := Hit_Astroid ||
                        currentGamestate := LOST
                    END
                ELSE
                    //If returned to starbase then the game is won
                    currentGamestate := WON ||
                    report := Game_Over
                 END
            ELSE
                 //Cannot move out of the Grid positions
                report := Error_OutOfBounds
            END
        ELSE
            //If no power to move then the game is lost
            currentGamestate := LOST ||
            report := Low_Power
        END
END
END;

//Operation to fire at the asteroids
report <-- Fire =
PRE
    currentGamestate = ONGOING
THEN
    //Check if the power of the spaceship is enough to fire
    IF spaceshipPower > ShootPower THEN
        IF spaceshipDirection = Right THEN
            spaceshipPower := spaceshipPower - ShootPower ||
            //Check if there is an asteroid present in the next grid position
            IF isSpaceShipAstroidCollision(spaceshipXPos + 1, spaceshipYPos) THEN
                report := Hit_Astroid ||
                noOfAstroidsDestroyed := noOfAstroidsDestroyed + 1 ||
                //Check if its a small asteroid
                IF isSmallAstroid(spaceshipXPos + 1, spaceshipYPos) THEN
                    smallAstroids := smallAstroids - {spaceshipXPos + 1 |-> spaceshipYPos}
                ELSE
                    //If its a large asteroid then a small asteroid is created in its place
                    largeAstroids := largeAstroids - {spaceshipXPos + 1 |-> spaceshipYPos} ||
                    smallAstroids := smallAstroids \/ {spaceshipXPos + 1 |-> spaceshipYPos}
                END
           ELSE
               //If no asteroid present then its a miss
                report := Miss
            END
        ELSIF spaceshipDirection = Left THEN
            spaceshipPower := spaceshipPower - ShootPower ||
             //Check if there is an asteroid present in the next grid position
             IF isSpaceShipAstroidCollision(spaceshipXPos - 1, spaceshipYPos) THEN
                report := Hit_Astroid ||
                noOfAstroidsDestroyed := noOfAstroidsDestroyed + 1 ||
                IF isSmallAstroid(spaceshipXPos - 1, spaceshipYPos) THEN
                    smallAstroids := smallAstroids - {spaceshipXPos - 1 |-> spaceshipYPos}
                ELSE
                    //If its a large asteroid then a small asteroid is created in its place
                    largeAstroids := largeAstroids - {spaceshipXPos - 1 |-> spaceshipYPos} ||
                    smallAstroids := smallAstroids \/ {spaceshipXPos - 1 |-> spaceshipYPos}
                END
           ELSE
               //If no asteroid present then its a miss
                report := Miss
            END
        ELSIF spaceshipDirection = Up THEN
            spaceshipPower := spaceshipPower - ShootPower ||
             //Check if there is an asteroid present in the next grid position
             IF isSpaceShipAstroidCollision(spaceshipXPos, spaceshipYPos + 1) THEN
                report := Hit_Astroid ||
                noOfAstroidsDestroyed := noOfAstroidsDestroyed + 1 ||
                IF isSmallAstroid(spaceshipXPos, spaceshipYPos - 1) THEN
                    smallAstroids := smallAstroids - {spaceshipXPos |-> spaceshipYPos + 1}
                ELSE
                    //If its a large asteroid then a small asteroid is created in its place
                    largeAstroids := largeAstroids - {spaceshipXPos |-> spaceshipYPos + 1} ||
                    smallAstroids := smallAstroids \/ {spaceshipXPos |-> spaceshipYPos + 1}
                END
           ELSE
               //If no asteroid present then its a miss
                report := Miss
            END
         ELSIF spaceshipDirection = Down THEN
            spaceshipPower := spaceshipPower - ShootPower ||
             //Check if there is an asteroid present in the next grid position
             IF isSpaceShipAstroidCollision(spaceshipXPos , spaceshipYPos - 1) THEN
                report := Hit_Astroid ||
                noOfAstroidsDestroyed := noOfAstroidsDestroyed + 1 ||
                IF isSmallAstroid(spaceshipXPos , spaceshipYPos - 1) THEN
                    smallAstroids := smallAstroids - {spaceshipXPos |-> spaceshipYPos - 1}
                ELSE
                    //If its a large asteroid then a small asteroid is created in its place
                    largeAstroids := largeAstroids - {spaceshipXPos |-> spaceshipYPos - 1} ||
                    smallAstroids := smallAstroids \/ {spaceshipXPos |-> spaceshipYPos - 1}
                END
           ELSE
               //If no asteroid present then its a miss
                report := Miss
            END
        END
    ELSE
        //If no power to fire
        report := Low_Power
     END
END;

//Operation to get the current game state, current location, current heading,current power and the number of asteroids destroyed
 stateOfGame, currentLocation, currentHeading, powerReserves, noOfAstDestroyed <-- Status =
 BEGIN
     //Check if the spaceship has returned to the starbase
     IF isReturnedToStarBase THEN
        currentGamestate := WON ||
        stateOfGame := WON ||
        currentLocation := spaceshipCurrentPos ||
        currentHeading := spaceshipDirection ||
        powerReserves := spaceshipPower ||
        noOfAstDestroyed := noOfAstroidsDestroyed
    //Check if the spaceship has power to move
    ELSIF spaceshipPower < MovePower THEN
        currentGamestate := LOST ||
        stateOfGame := LOST ||
        currentLocation := spaceshipCurrentPos ||
        currentHeading := spaceshipDirection ||
        powerReserves := spaceshipPower ||
        noOfAstDestroyed := noOfAstroidsDestroyed
     ELSE
        stateOfGame := currentGamestate ||
        currentLocation := spaceshipCurrentPos ||
        currentHeading := spaceshipDirection ||
        powerReserves := spaceshipPower ||
        noOfAstDestroyed := noOfAstroidsDestroyed
     END
END
END
