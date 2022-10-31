/* Space Ship
 * Author: USER
 * Creation date: 11/24/2021
 */
MACHINE
    SpaceShip   
    
SETS
    MESSAGE = {Hit_Asteroid, Cannot_Warp_Asteroid, SuccessfullyMoved,SpaceshipCannotMove,InsufficientPower,Cannot_Warp_Same_Position,Cannot_Warp_StartBase};
    SPACESHIP_MOVEMENT = {Move_Up,Move_Down,Move_Backward,Move_Foward,Spaceship_Warp};
    DOCKED_STATUS = {YES, NO};
    STATUS = {Game_Not_Over,Game_Won,Game_Lost}
    
CONSTANTS
    normalMovingPower, warpDrivingPower, asteroidCrashPowerLoss, initiativePower, areaX, areaY, area, asteroids, emptyArea, spaceshipHomeBase, spaceshipStarBase
    
PROPERTIES
    warpDrivingPower = 20 &
    asteroidCrashPowerLoss = 10 &
    initiativePower = 100 &
    areaX = 1..12 &
    areaY = 1..7 &
    normalMovingPower = 5 &
    area = areaX * areaY &
    emptyArea <: area &
    emptyArea /\ asteroids = {} &
    emptyArea \/ asteroids = area &
    asteroids <: area &
    asteroids = {3|->2, 3|->5, 5|->4, 6|->7, 7|->1, 7|->5, 7|->7, 8|->3, 10|->6, 11|->2, 12|->5} &
    spaceshipHomeBase : emptyArea & spaceshipHomeBase = 1|->1 &
    spaceshipStarBase : emptyArea & spaceshipStarBase = 6|->4
    
DEFINITIONS
    isWithinTheSpace(xxCordinate, yyCordinate) == (xxCordinate |-> yyCordinate : area);
    isCrashAsteroid(xxCordinate, yyCordinate) == (xxCordinate |-> yyCordinate : asteroids);
    hasEnoughSpaceshipPower(xp, yp) == (xp >= yp);
    isGameDocked == (xCordinate |-> yCordinate = spaceshipStarBase);
    isGameOver == isGameDocked or (spaceshipPower < normalMovingPower)
    
    
VARIABLES
    xCordinate, yCordinate, spaceshipPower, collisionsCount, routeUse, spaceshipMovements
    
INVARIANT
    xCordinate : areaX &
    yCordinate : areaY &
    xCordinate |-> yCordinate : emptyArea &
    spaceshipPower : NAT &
    collisionsCount : NAT &
    routeUse : seq(emptyArea) &
    spaceshipMovements : seq(SPACESHIP_MOVEMENT)
    
INITIALISATION
    spaceshipPower := initiativePower ||
    collisionsCount := 0 ||
    xCordinate := prj1(areaX, areaY)(spaceshipHomeBase) ||
    yCordinate := prj2(areaX, areaY)(spaceshipHomeBase) ||
    routeUse := [spaceshipHomeBase] ||
    spaceshipMovements := []
    
OPERATIONS
    message, spaceshiMovement <-- MoveUp =
    PRE
        message : MESSAGE & spaceshiMovement : SPACESHIP_MOVEMENT & not(isGameOver)
    THEN
        IF
            hasEnoughSpaceshipPower(spaceshipPower, normalMovingPower)
        THEN
            IF
                isWithinTheSpace(xCordinate, yCordinate + 1)
            THEN
                IF 
                    not(isCrashAsteroid(xCordinate, yCordinate + 1))
                THEN
                    IF
                        (spaceshipPower - normalMovingPower >= 0)
                    THEN
                        yCordinate := yCordinate + 1 ||
                        spaceshipPower := spaceshipPower - normalMovingPower ||
                        routeUse := routeUse <- (xCordinate |-> yCordinate + 1) ||
                        spaceshipMovements := spaceshipMovements <- Move_Up ||
                        message := SuccessfullyMoved ||
                        spaceshiMovement := Move_Up
                    ELSE
                        yCordinate := yCordinate + 1 ||
                        spaceshipPower := 0 ||
                        routeUse := routeUse <- (xCordinate |-> yCordinate + 1) ||
                        spaceshipMovements := spaceshipMovements <- Move_Up ||
                        message := SuccessfullyMoved ||
                        spaceshiMovement := Move_Up
                    END
                ELSE
                    IF
                        (spaceshipPower - normalMovingPower - asteroidCrashPowerLoss >= 0)
                    THEN
                        spaceshipPower := spaceshipPower - normalMovingPower - asteroidCrashPowerLoss ||
                        collisionsCount := collisionsCount + 1 ||
                        message := Hit_Asteroid ||
                        spaceshiMovement := Move_Up
                    ELSE
                        spaceshipPower := 0 ||
                        collisionsCount := collisionsCount + 1 ||
                        message := Hit_Asteroid ||
                        spaceshiMovement := Move_Up
                    END
                END
            ELSE
                message := SpaceshipCannotMove
            END
        ELSE
            message := InsufficientPower
        END
    END;
    
    message, spaceshiMovement <-- MoveDown =
    PRE
        message : MESSAGE & spaceshiMovement : SPACESHIP_MOVEMENT & not(isGameOver)
    THEN
        IF
            hasEnoughSpaceshipPower(spaceshipPower, normalMovingPower)
        THEN
            IF
                isWithinTheSpace(xCordinate, yCordinate - 1)
            THEN
                IF 
                    not(isCrashAsteroid(xCordinate, yCordinate - 1))
                THEN
                    IF
                        (spaceshipPower - normalMovingPower >= 0)
                    THEN
                        yCordinate := yCordinate - 1 ||
                        spaceshipPower := spaceshipPower - normalMovingPower ||
                        routeUse := routeUse <- (xCordinate |-> yCordinate - 1) ||
                        spaceshipMovements := spaceshipMovements <- Move_Down ||
                        message :=  SuccessfullyMoved ||
                        spaceshiMovement := Move_Down
                    ELSE
                        yCordinate := yCordinate - 1 ||
                        spaceshipPower := 0 ||
                        routeUse := routeUse <- (xCordinate |-> yCordinate - 1) ||
                        spaceshipMovements := spaceshipMovements <- Move_Down ||
                        message :=  SuccessfullyMoved ||
                        spaceshiMovement := Move_Down
                    END
                ELSE
                    IF
                        (spaceshipPower - normalMovingPower - asteroidCrashPowerLoss >= 0)
                    THEN
                        spaceshipPower := spaceshipPower - normalMovingPower - asteroidCrashPowerLoss ||
                        collisionsCount := collisionsCount + 1 ||
                        message := Hit_Asteroid ||
                        spaceshiMovement := Move_Down
                    ELSE
                        spaceshipPower := 0 ||
                        collisionsCount := collisionsCount + 1 ||
                        message := Hit_Asteroid ||
                        spaceshiMovement := Move_Down
                    END
                END
            ELSE
                message := SpaceshipCannotMove
            END
        ELSE
            message := InsufficientPower
        END   
    END;
    
    message, spaceshiMovement <-- MoveForward =
    PRE
        message : MESSAGE & spaceshiMovement : SPACESHIP_MOVEMENT & not(isGameOver)
    THEN
        IF
            hasEnoughSpaceshipPower(spaceshipPower, normalMovingPower)
        THEN
            IF
                isWithinTheSpace(xCordinate + 1, yCordinate)
            THEN
                IF 
                    not(isCrashAsteroid(xCordinate + 1, yCordinate))
                THEN
                    IF
                        (spaceshipPower -normalMovingPower >= 0)
                    THEN
                        xCordinate := xCordinate + 1 ||
                        spaceshipPower := spaceshipPower - normalMovingPower ||
                        routeUse := routeUse <- (xCordinate + 1 |-> yCordinate) ||
                        spaceshipMovements := spaceshipMovements <- Move_Foward ||
                        message :=  SuccessfullyMoved ||
                        spaceshiMovement := Move_Foward
                    ELSE
                        xCordinate := xCordinate + 1 ||
                        spaceshipPower := 0 ||
                        routeUse := routeUse <- (xCordinate + 1 |-> yCordinate) ||
                        spaceshipMovements := spaceshipMovements <- Move_Foward ||
                        message :=  SuccessfullyMoved ||
                        spaceshiMovement := Move_Foward
                    END
                ELSE
                    IF
                        (spaceshipPower - normalMovingPower - asteroidCrashPowerLoss >= 0)
                    THEN
                        spaceshipPower := spaceshipPower - normalMovingPower - asteroidCrashPowerLoss ||
                        collisionsCount := collisionsCount + 1 ||
                        message := Hit_Asteroid ||
                        spaceshiMovement := Move_Foward
                    ELSE
                        spaceshipPower := 0 ||
                        collisionsCount:= collisionsCount + 1 ||
                        message := Hit_Asteroid ||
                        spaceshiMovement := Move_Foward
                    END
                END
            ELSE
                message := SpaceshipCannotMove
            END
        ELSE
            message := InsufficientPower
        END   
    END;
    
    message, spaceshiMovement <-- MoveBackward =
    PRE
        message : MESSAGE & spaceshiMovement : SPACESHIP_MOVEMENT & not(isGameOver)
    THEN
        IF
            hasEnoughSpaceshipPower(spaceshipPower, normalMovingPower)
        THEN
            IF
                isWithinTheSpace(xCordinate - 1, yCordinate)
            THEN
                IF 
                    not(isCrashAsteroid(xCordinate - 1, yCordinate))
                THEN
                    IF
                        (spaceshipPower - normalMovingPower >= 0)
                    THEN
                        xCordinate := xCordinate - 1 ||
                        spaceshipPower := spaceshipPower - normalMovingPower ||
                        routeUse := routeUse <- (xCordinate - 1 |-> yCordinate) ||
                        spaceshipMovements := spaceshipMovements <- Move_Backward ||
                        message :=  SuccessfullyMoved ||
                        spaceshiMovement := Move_Backward
                    ELSE
                        xCordinate := xCordinate - 1 ||
                        spaceshipPower := 0 ||
                        routeUse := routeUse <- (xCordinate - 1 |-> yCordinate) ||
                        spaceshipMovements := spaceshipMovements <- Move_Backward ||
                        message :=  SuccessfullyMoved ||
                        spaceshiMovement := Move_Backward
                    END
                ELSE
                    IF
                        (spaceshipPower - normalMovingPower - asteroidCrashPowerLoss >= 0)
                    THEN
                        spaceshipPower := spaceshipPower - normalMovingPower - asteroidCrashPowerLoss ||
                        collisionsCount := collisionsCount + 1 ||
                        message := Hit_Asteroid ||
                        spaceshiMovement := Move_Backward
                    ELSE
                        spaceshipPower := 0 ||
                        collisionsCount := collisionsCount + 1 ||
                        message := Hit_Asteroid ||
                        spaceshiMovement := Move_Backward
                    END
                END
            ELSE
                message := SpaceshipCannotMove
            END
        ELSE
            message := InsufficientPower
        END   
    END;
    
    message, spaceshiMovement <-- EngageWarpDrive(newXCordinate, newYCordinate) =
    PRE
        message : MESSAGE & spaceshiMovement : SPACESHIP_MOVEMENT &
        newXCordinate : NAT1 & newYCordinate : NAT1 &
        not(isGameOver)
    THEN
        IF
            hasEnoughSpaceshipPower(spaceshipPower, warpDrivingPower)
        THEN
            IF
                isWithinTheSpace( newXCordinate, newYCordinate)
            THEN
                IF
                    (newXCordinate = xCordinate & newYCordinate = yCordinate)
                THEN
                    message := Cannot_Warp_Same_Position
                ELSE
                    IF 
                        (size(routeUse) = 1 & newXCordinate|->newYCordinate = spaceshipStarBase)
                    THEN
                        message := Cannot_Warp_StartBase
                    ELSE
                        IF 
                            not(isCrashAsteroid(newXCordinate, newYCordinate))
                        THEN
                            IF
                                (spaceshipPower - warpDrivingPower >= 0)
                            THEN
                                spaceshipPower := spaceshipPower - warpDrivingPower ||
                                xCordinate := newXCordinate ||
                                yCordinate := newYCordinate ||
                                routeUse := routeUse <- (newXCordinate |-> newYCordinate) ||
                                spaceshipMovements := spaceshipMovements <- Spaceship_Warp ||
                                message :=  SuccessfullyMoved ||
                                spaceshiMovement := Spaceship_Warp
                            ELSE
                                spaceshipPower := 0 ||
                                xCordinate := newXCordinate ||
                                yCordinate := newYCordinate ||
                                routeUse := routeUse <- (newXCordinate |->newYCordinate) ||
                                spaceshipMovements := spaceshipMovements <- Spaceship_Warp ||
                                message :=  SuccessfullyMoved ||
                                spaceshiMovement := Spaceship_Warp
                            END
                        ELSE
                            message := Cannot_Warp_Asteroid
                        END
                    END
                END
            ELSE
                message := SpaceshipCannotMove
            END
        ELSE
            message := InsufficientPower
        END        
    END;
    
    currentLocation, currentPower, asteroidCollisions <-- MissionStatus =
    BEGIN
        currentLocation := xCordinate |-> yCordinate ||
        currentPower := spaceshipPower ||
        asteroidCollisions := collisionsCount
    END;
    
    route <-- MissionRoute =
    BEGIN
        route := routeUse
    END;
    
    gameDockedStatus <-- DockedAtStarbase =
    PRE
        gameDockedStatus : DOCKED_STATUS
    THEN
        IF
            (isGameDocked)
        THEN
            gameDockedStatus := YES
        ELSE
            gameDockedStatus := NO
        END
    END;
    
    status <-- GameStatus =
    PRE
        status : STATUS
    THEN
        IF
            (isGameDocked)
        THEN
            status := Game_Won
        ELSE
            IF
                (spaceshipPower < normalMovingPower)
            THEN
                status := Game_Lost
            ELSE
                status := Game_Not_Over
            END
        END
    END;
    
    allSpaceshipMovements <-- MovementsUse =
    BEGIN
        allSpaceshipMovements := spaceshipMovements
    END;
    
    NewGame =
    PRE
        isGameOver
    THEN
        spaceshipPower := initiativePower ||
        collisionsCount := 0 ||
        xCordinate := prj1(areaX, areaY)(spaceshipHomeBase) ||
        yCordinate := prj2(areaX, areaY)(spaceshipHomeBase) ||
        routeUse := [spaceshipHomeBase] ||
        spaceshipMovements := []
    END
END