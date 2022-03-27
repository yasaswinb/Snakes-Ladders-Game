/* SnakeAndLadders
 * Author: Yasaswin
 * Creation date: 2022-01-21
 */
MACHINE
    SnakeAndLadders

SETS

    GAME_REPORTS = { Went_Down_a_Snake , Up_a_Ladder , Threw_Too_High_Dice_Value_to_Finish , Finish_And_Won , Landed_on_A_Normal_Square , New_Game_Started }

CONCRETE_CONSTANTS

    BOARD ,
    snakes ,
    ladders

PROPERTIES

    BOARD = 0 .. 100 & BOARD <: NAT &
    snakes : BOARD >+> BOARD & snakes = { ( 97 |-> 75 ) , ( 63 |-> 60 ) , ( 66 |-> 52 ) , ( 47 |-> 25 ) , ( 31 |-> 4 ) , ( 16 |-> 13 ) } & card ( snakes ) = 6 &
    ladders : BOARD >+> BOARD & ladders = { ( 61 |-> 99 ) , ( 56 |-> 84 ) , ( 72 |-> 90 ) , ( 27 |-> 53 ) , ( 3 |-> 39 ) , ( 10 |-> 12 ) } & card ( ladders ) = 6 &
    dom ( snakes ) /<: ran ( ladders ) & dom ( ladders ) /<: ran ( snakes )

DEFINITIONS

    isWon ( current_square ) == ( current_square = 100 )

ABSTRACT_VARIABLES

    current_position ,
    last_thrown_dice_value ,
    num_of_moves ,
    num_of_snakes_gone_down ,
    num_of_ladders_gone_up ,
    list_of_squares_visited


INVARIANT

    current_position : BOARD & current_position : NAT &
    last_thrown_dice_value : 0 .. 6 & last_thrown_dice_value : NAT &
    num_of_moves : NAT &
    num_of_snakes_gone_down : NAT &
    num_of_ladders_gone_up : NAT &
    list_of_squares_visited : seq ( BOARD )

INITIALISATION

    current_position := 0 ||
    last_thrown_dice_value := 0 ||
    num_of_moves := 0 ||
    num_of_snakes_gone_down := 0 ||
    num_of_ladders_gone_up := 0 ||
    list_of_squares_visited := []

OPERATIONS

    statReport <-- Move ( dice ) =
    PRE dice : NAT1 & dice : 1 .. 6 & statReport : GAME_REPORTS & not ( isWon ( current_position ) )
    THEN
        IF ( ( ( current_position + dice ) /: BOARD ) & not ( isWon ( current_position + dice ) ) )
        THEN
            statReport :=  Threw_Too_High_Dice_Value_to_Finish ||
            last_thrown_dice_value := dice

        ELSE
            IF ( current_position + dice : dom ( snakes ) & not ( isWon ( current_position + dice ) ) )
            THEN
                current_position := snakes ( current_position + dice ) ||
                last_thrown_dice_value := dice ||
                num_of_moves := succ ( num_of_moves ) ||
                num_of_snakes_gone_down := succ ( num_of_snakes_gone_down ) ||
                list_of_squares_visited := list_of_squares_visited ^ [ current_position + dice , snakes ( current_position + dice ) ] ||
                statReport :=  Went_Down_a_Snake

            ELSIF ( current_position + dice : dom ( ladders ) & not ( isWon ( current_position + dice ) ) )
             THEN
                current_position := ladders ( current_position + dice ) ||
                last_thrown_dice_value := dice ||
                num_of_moves := succ ( num_of_moves ) ||
                num_of_ladders_gone_up := succ ( num_of_ladders_gone_up ) ||
                list_of_squares_visited := list_of_squares_visited ^ [ current_position + dice , ladders ( current_position + dice ) ] ||
                statReport :=  Up_a_Ladder

            ELSIF ( isWon ( current_position + dice ) )
             THEN
                current_position := current_position + dice ||
                last_thrown_dice_value := dice ||
                num_of_moves := succ ( num_of_moves ) ||
                num_of_ladders_gone_up := succ ( num_of_ladders_gone_up ) ||
                list_of_squares_visited := list_of_squares_visited <- ( current_position + dice ) ||
                statReport :=  Finish_And_Won

            ELSE
                current_position := current_position + dice ||
                last_thrown_dice_value := dice ||
                num_of_moves := succ ( num_of_moves ) ||
                list_of_squares_visited := list_of_squares_visited <- ( current_position + dice ) ||
                statReport :=  Landed_on_A_Normal_Square

            END
        END
    END ;

    current_position_msg , num_of_snakes_gone_down_msg , num_of_ladders_gone_up_msg , num_of_moves_msg <-- GameStatistics =
    BEGIN
      current_position_msg := current_position ||
      num_of_snakes_gone_down_msg := num_of_snakes_gone_down ||
      num_of_ladders_gone_up_msg := num_of_ladders_gone_up ||
      num_of_moves_msg := num_of_moves
    END ;

    list_of_squares_visited_output <-- VisitedSquares =
    BEGIN
        list_of_squares_visited_output := list_of_squares_visited
    END ;

    statReport <-- NewGame =
    PRE statReport : GAME_REPORTS & size ( list_of_squares_visited ) > 0
    THEN
        statReport := New_Game_Started ||
        current_position := 0 ||
        last_thrown_dice_value := 0 ||
        num_of_moves := 0 ||
        num_of_snakes_gone_down := 0 ||
        num_of_ladders_gone_up := 0 ||
        list_of_squares_visited := []
    END

END
