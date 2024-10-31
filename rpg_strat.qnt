module rpg {
    import rareSpells.* from "./spells/rareSpells"
    import basicSpells.* from "./spells/basicSpells"

    type CreatureClass = Wizard | Hunter | Druid | Illusion | Monster

    type Creature = {
        id: str,
        hp: int,
        initiative: int,
        class: CreatureClass,
        status: { blind: bool, wild: bool, paralised: bool },
        extra_hp: int,
    }

    type MoveDescription =
        | Attack({creature: Creature, receiver: Creature, damage: int})
        | Paralise({creature: Creature, receiver: Creature})
        | Blind({creature: Creature, receiver: Creature})
        | Unparalise({creature: Creature, receiver: Creature})
        | CastIllusion(Creature)
        | WildShape(Creature)
        | Skip(Creature)
        | Dead(Creature)

    pure def damaged(receiver: Creature, damage: int): Creature = {
        if (receiver.status.wild)
            {...receiver, extra_hp: receiver.extra_hp - damage}
        else    
            {...receiver, hp: receiver.hp - damage}
    }

    pure def blinded(receiver: Creature): Creature = {
        {...receiver, status: {...receiver.status, blind: true}}
    }

    pure def unblinded(receiver: Creature): Creature = {
        {...receiver, status: {...receiver.status, blind: false}}
    }

    pure def castedWildShape(character: Creature): Creature = {
        {...character, extra_hp: 60, status: {...character.status, wild: true}}
    }

    pure def notParalised(character: Creature): Creature = {
        {...character, status: {...character.status, paralised: false}}
    }

    pure def paralised(character: Creature): Creature = {
        {...character, status: {...character.status, paralised: true}}
    }

    pure def isMonster(creature: Creature): bool = {
        creature.class == Monster
    }

    pure def isCharacter(creature: Creature): bool = {
        or {
            creature.class == Wizard,
            creature.class == Hunter,
            creature.class == Druid,
        }
    }

    pure def isThreat(creature: Creature): bool = {
        or {
            and {
                creature.status.wild,
                creature.extra_hp > 0,
            },
            and {
                creature.isAlive(),
                creature.isIllusion(),
            }
        }
    }

    pure def removeWild(character: Creature): Creature = {
        {...character, extra_hp: 0, status: {...character.status, wild: false}}
    }

    pure def isIllusion(creature: Creature): bool = {
        creature.class == Illusion
    }

    pure def isAlive(creature: Creature): bool = {
        creature.hp > 0
    }

    pure def isParalised(creature: Creature): bool = {
        creature.status.paralised
    }

    pure def isBlind(creature: Creature): bool = {
        creature.status.blind
    }

    pure def setInitiative(creature: Creature, initiative: int): Creature = {
        {...creature, initiative: initiative}
    }

    def uncastSpells(character: Creature): (Creature, Set[Creature]) = {
        if (character.status.wild) {
            val restoredChar = character.removeWild()
            (restoredChar, creatures.map(c => if (c == character) restoredChar else c))
        } else if (character.class == Wizard) {
            (character, creatures.filter(c => not(c.isIllusion())))
        } else {
            (character, creatures.map(c => if (c.status.wild and c.extra_hp <= 0) c.removeWild() else c))
        }
    }

    pure val createIllusion: Creature = {
        {id: "Sheep", hp: 1, initiative: 0, class: Illusion, extra_hp: 0, status: {blind: false, wild: false, paralised: false}}
    }

    // Pergunta para a professora porque que ela usou pure val
    pure val CREATURES: Set[Creature] = Set( 
        { id: "Wizard", hp: 20, initiative: 0, class: Wizard, extra_hp: 0, status: { blind: false, wild: false, paralised: false } },
        { id: "Hunter", hp: 20, initiative: 0, class: Hunter, extra_hp: 0, status: { blind: false, wild: false, paralised: false } },
        { id: "Druid", hp: 20, initiative: 0, class: Druid, extra_hp: 0, status: { blind: false, wild: false, paralised: false } },
        { id: "Monster_1", hp: 100, initiative: 0, class: Monster, extra_hp: 0, status: { blind: false, wild: false, paralised: false } },
        { id: "Monster_2", hp: 100, initiative: 0, class: Monster, extra_hp: 0, status: { blind: false, wild: false, paralised: false } }
    )

    var creatures: Set[Creature]
    var turn: int
    var lastMove: Option[MoveDescription]

    pure val d20 = 1.to(20)
    val monsters = creatures.filter(c => c.isMonster())
    val characters = creatures.filter(c => c.isCharacter())
    val threats = creatures.filter(c => c.isThreat())
    val threatsExist = creatures.exists(c => c.isThreat())
    val creatures_by_initiative = creatures.filter(c => not(c.isIllusion())).toList((c1, c2) => intCompare(c2.initiative, c1.initiative))

    action paralise(monster: Creature, receiver: Creature): bool = {
        all {
            receiver.isAlive(),
            any {
                receiver.isCharacter(),
                receiver.isIllusion(),
            },
            not(receiver.isParalised()),
            creatures' = creatures.map(c => if(c == receiver) c.paralised() else c).map(c => if(c == monster) c.unblinded() else c),
            lastMove' = Some(Paralise({creature: monster, receiver: receiver})),
        }
    }

    action monsterAttack(monster: Creature, receiver: Creature): bool = {
        val damage = if ( monster.isBlind() ) 0 else if ( turn == 0 ) 10 else 20
        all {
            receiver.isAlive(),
            any {
                receiver.isCharacter(),
                receiver.isIllusion()
            },
            creatures' = creatures.map(c => if(c == receiver) c.damaged(damage) else c).map(c => if(c == monster) c.unblinded() else c),
            lastMove' = Some(Attack({creature: monster, receiver: receiver, damage: damage})),
        }
    }

    action monsterTurn(monster: Creature): bool = {
        val receiverSet = if (threatsExist) threats else characters
        nondet receiver = receiverSet.oneOf()
        all {
            monster.isMonster(),
            any {
                monsterAttack(monster, receiver),
                paralise(monster, receiver),
            }
        }
    }

    action removeParalisis(character: Creature, receiver: Creature, auxCreatureSet: Set[Creature]): bool = {
        all {
            character != receiver,
            receiver.isCharacter(),
            receiver.isParalised(),
            receiver.isAlive(),
            creatures' = auxCreatureSet.map(c => if (c == receiver) c.notParalised() else c),
            lastMove' = Some(Unparalise({creature: character, receiver: receiver}))
        }
    }

    //
    action characterAttack(character: Creature, receiver: Creature, auxCreatureSet: Set[Creature]): bool = {
        all {
            receiver.isMonster(),
            receiver.isAlive(),
            creatures' = auxCreatureSet.map(c => if (c == receiver) c.damaged(10) else c),
            lastMove' = Some(Attack({creature: character, receiver: receiver, damage: 10})),
        }
    }

    action illusion(character: Creature, auxCreatureSet: Set[Creature]): bool = {
        all {
            character.class == Wizard,
            creatures' = auxCreatureSet.union(Set(createIllusion)),
            lastMove' = Some(CastIllusion(character))
        }
    }

    action wildShape(character: Creature, auxCreatureSet: Set[Creature]): bool = {
        all {
            character.class == Druid,
            creatures' = auxCreatureSet.map(c => if (c == character) c.castedWildShape() else c),
            lastMove' = Some(WildShape(character))
        }
    }

    action blind(character: Creature, receiver: Creature, auxCreatureSet: Set[Creature]): bool = {
        all {
            character.class == Hunter,
            receiver.isMonster(),
            not(receiver.isBlind()),
            creatures' = auxCreatureSet.map(c => if(c == receiver) c.blinded() else c),
            lastMove' = Some(Blind({creature: character, receiver: receiver})),
        }
    }

    action characterTurn(character: Creature): bool = {
        val tuple = uncastSpells(character)
        val restoredChar = tuple._1
        val auxCreatureSet = tuple._2
        val noThreats = not(auxCreatureSet.exists(c => c.isThreat()))
        val paralisedChars = auxCreatureSet.filter(c => c.isCharacter() and c.isParalised())
        val someoneIsParalised = auxCreatureSet.exists(c => c.isCharacter() and c.isParalised())
        val monsters = auxCreatureSet.filter(c => c.isMonster())

        def everyoneElseParalised(character: Creature): bool = {
            auxCreatureSet.filter(c => c != character).forall(c => c.isParalised())
        } 

        all {
            restoredChar.isCharacter(),

            if ( restoredChar.isParalised() ) 
                all {
                    creatures' = auxCreatureSet,
                    lastMove' = Some(Skip(restoredChar)),
                } 
            
            else if ( someoneIsParalised )
                nondet receiver = paralisedChars.oneOf()
                removeParalisis(restoredChar, receiver, auxCreatureSet)

            else if ( noThreats )
                nondet monster = monsters.oneOf()
                any {
                    blind(restoredChar, monster, auxCreatureSet),
                    wildShape(restoredChar, auxCreatureSet),
                    illusion(restoredChar, auxCreatureSet),
                }
            
            else
                nondet monster = monsters.oneOf()
                characterAttack(restoredChar, monster, auxCreatureSet)
        }
    }

    //
    action init = {
        nondet wizardRoll = d20.oneOf()
        nondet hunterRoll = d20.oneOf()
        nondet druidRoll = d20.oneOf()
        nondet monsterRoll = d20.oneOf()
        
        def initiativeAux(creature: Creature): Creature = {
            if (creature.class == Wizard) creature.setInitiative(wizardRoll) else
            if (creature.class == Hunter) creature.setInitiative(hunterRoll) else
            if (creature.class == Druid) creature.setInitiative(druidRoll) else
            creature.setInitiative(monsterRoll)
        }

        all {
            creatures' = CREATURES.map(initiativeAux),
            turn' = 0,
            lastMove' = None
        }
    }

    action step = {
        val playingCreature = creatures_by_initiative[turn % creatures.filter(c => not(c.isIllusion())).size()]
        
        if ( playingCreature.isAlive() ) {
            all {
                any {
                    characterTurn(playingCreature),
                    monsterTurn(playingCreature),
                },
                turn' = turn + 1
            }
        } else {
            all {
                creatures' = creatures,
                lastMove' = Some(Dead(playingCreature)),
                turn' = turn + 1,
            }
        }
    }

    val noCharsDie = characters.forall(c => c.isAlive())
    val noMonstersDie = monsters.forall(m => m.isAlive())
}