MACHINE Battleships  // Machine definition for a naval combat simulation

SETS
    /* Participants in the maritime battle */
    CombatParticipants = {Commander1, Commander2};
    
    /* Coordinate system for the naval grid */
    NavGridHorizontal = {H1, H2, H3, H4, H5, H6, H7, H8, H9, H10};
    NavGridVertical = {V1, V2, V3, V4, V5, V6, V7, V8, V9, V10};
    
    /* Progression stages of the naval engagement */
    BattlePhase = {conflict_uninitialized, commander1_positioning, commander2_positioning, battle_active, conflict_resolved};
    
    /* Communication signals about battle progression */
    BattleUpdateSignal = {
        fleet_preparation_needed,
        commander1_fleet_ready,
        commander2_fleet_ready,
        battle_ongoing_commander1,
        battle_ongoing_commander2,
        commander1_triumph,
        commander2_triumph,
        strategic_stalemate
    };
    
    /* Outcome classification of tactical actions */
    CombatResult = {action_accomplished, action_strike, action_miss, action_neutral};
    
    /* Potential conflict resolution */
    ConflictOutcome = {victor_commander1, victor_commander2, no_victor}

CONSTANTS
    /* Maximum naval vessels permitted */
    MAX_VESSELS,
    
    /* Complete maritime engagement area */
    NAVAL_GRID

PROPERTIES
    /* Vessel count limitation */
    MAX_VESSELS = 3 &
    
    /* Naval grid defined by coordinate intersection */
    NAVAL_GRID = NavGridHorizontal * NavGridVertical

VARIABLES
    /* Commander 1's vessel placement */
    commander1_vessel_grid,
    
    /* Commander 2's vessel placement */
    commander2_vessel_grid,
    
    /* Current commanding participant */
    active_battle_commander,
    
    /* Present conflict progression stage */
    current_battle_phase,
    
    /* Tactical strikes by Commander 1 */
    commander1_strike_count,
    
    /* Tactical strikes by Commander 2 */
    commander2_strike_count,
    
    /* Conflict resolution designation */
    battle_victor,
    
    /* Narrative summary of conflict outcome */
    battle_conclusion_status

INVARIANT
    /* Vessel placements constrained within naval grid */
    commander1_vessel_grid <: NAVAL_GRID &
    commander2_vessel_grid <: NAVAL_GRID &
    
    /* Vessel deployment quantity restriction */
    card(commander1_vessel_grid) <= MAX_VESSELS &
    card(commander2_vessel_grid) <= MAX_VESSELS &
    
    /* Active commander validation */
    active_battle_commander : CombatParticipants &
    
    /* Battle progression stage validation */
    current_battle_phase : BattlePhase &
    
    /* Strike tallies as non-negative integers */
    commander1_strike_count : NAT &
    commander2_strike_count : NAT &
    
    /* Preventing vessel overlap between commanders */
    commander1_vessel_grid /\ commander2_vessel_grid = {} &
    
    /* Victor determination validation */
    battle_victor : ConflictOutcome &
    
    /* Conflict status message validation */
    battle_conclusion_status : BattleUpdateSignal

INITIALISATION
    /* Establish initial conflict parameters */
    commander1_vessel_grid := {} ||
    commander2_vessel_grid := {} ||
    active_battle_commander := Commander1 ||
    current_battle_phase := conflict_uninitialized ||
    commander1_strike_count := 0 ||
    commander2_strike_count := 0 ||
    battle_victor := no_victor ||
    battle_conclusion_status := fleet_preparation_needed

OPERATIONS
    /* Deploy naval fleet for a specific commander */
    result <-- deployFleet(battle_commander, vessel_positions) =
    PRE
        /* Deployment validation conditions */
        battle_commander : CombatParticipants &
        vessel_positions <: NAVAL_GRID &
        card(vessel_positions) = MAX_VESSELS &
        vessel_positions /\ NAVAL_GRID = vessel_positions &
        (battle_commander = Commander1 => current_battle_phase = conflict_uninitialized) &
        (battle_commander = Commander2 => current_battle_phase = commander1_positioning)
    THEN
        /* Update grid and battle phase based on commander's deployment */
        IF battle_commander = Commander1 THEN
            commander1_vessel_grid := vessel_positions ||
            current_battle_phase := commander1_positioning ||
            result := action_accomplished
        ELSE
            commander2_vessel_grid := vessel_positions ||
            current_battle_phase := battle_active ||
            active_battle_commander := Commander1 ||
            result := action_accomplished
        END
    END;

    /* Tactical strike at a specific grid location */
    battle_strike_result <-- performStrike(target_grid_location) =
    PRE
        /* Strike targeting validation */
        target_grid_location : NAVAL_GRID &
        current_battle_phase = battle_active
    THEN
        /* Handle Commander 1's tactical engagement */
        IF active_battle_commander = Commander1 THEN
            IF target_grid_location : commander2_vessel_grid THEN
                /* Successful strike detected */
                commander2_vessel_grid := commander2_vessel_grid - {target_grid_location} ||
                commander1_strike_count := commander1_strike_count + 1 ||
                battle_strike_result := action_strike
            ELSE
                /* Missed strike, transfer tactical initiative */
                battle_strike_result := action_miss ||
                active_battle_commander := Commander2 ||
                commander1_strike_count := commander1_strike_count + 1
            END
        ELSE
            /* Handle Commander 2's tactical engagement */
            IF target_grid_location : commander1_vessel_grid THEN
                commander1_vessel_grid := commander1_vessel_grid - {target_grid_location} ||
                commander2_strike_count := commander2_strike_count + 1 ||
                battle_strike_result := action_strike
            ELSE
                battle_strike_result := action_miss ||
                active_battle_commander := Commander1 ||
                commander2_strike_count := commander2_strike_count + 1
            END
        END
    END;

    /* Evaluate and update conflict resolution */
    updateConflictStatus =
    BEGIN
        IF card(commander1_vessel_grid) = 0 THEN
            battle_conclusion_status := commander2_triumph
        ELSIF card(commander2_vessel_grid) = 0 THEN
            battle_conclusion_status := commander1_triumph
        END
    END;

    /* Retrieve current vessel locations for a commander */
    current_vessel_locations <-- getVesselPositions(battle_commander) =
    PRE
        battle_commander : CombatParticipants
    THEN
        IF battle_commander = Commander1 THEN
            current_vessel_locations := commander1_vessel_grid
        ELSE
            current_vessel_locations := commander2_vessel_grid
        END
    END;

    /* Count remaining vessels for a commander */
    remaining_vessels <-- countRemainingVessels(battle_commander) =
    PRE
        battle_commander : CombatParticipants
    THEN
        IF battle_commander = Commander1 THEN
            remaining_vessels := card(commander1_vessel_grid)
        ELSE
            remaining_vessels := card(commander2_vessel_grid)
        END
    END;

    /* Retrieve strike count for a commander */
    conducted_strikes <-- getStrikeCount(battle_commander) =
    PRE
        battle_commander : CombatParticipants
    THEN
        IF battle_commander = Commander1 THEN
            conducted_strikes := commander1_strike_count
        ELSE
            conducted_strikes := commander2_strike_count
        END
    END;

    /* Assess current battle progression status */
    current_status <-- evaluateBattleStatus =
    BEGIN
        IF current_battle_phase = conflict_uninitialized THEN
            current_status := fleet_preparation_needed
        ELSIF current_battle_phase = commander1_positioning THEN
            current_status := commander1_fleet_ready
        ELSIF current_battle_phase = commander2_positioning THEN
            current_status := commander2_fleet_ready
        ELSIF current_battle_phase = battle_active THEN
            IF active_battle_commander = Commander1 THEN
                current_status := battle_ongoing_commander1
            ELSE
                current_status := battle_ongoing_commander2
            END
        ELSIF current_battle_phase = conflict_resolved THEN
            IF battle_victor = victor_commander1 THEN
                current_status := commander1_triumph
            ELSIF battle_victor = victor_commander2 THEN
                current_status := commander2_triumph
            ELSE
                current_status := strategic_stalemate
            END
        END
    END;

    /* Retrieve final conflict outcome message */
    result_message <-- getConflictOutcomeMessage =
    BEGIN
        result_message := battle_conclusion_status
    END
END