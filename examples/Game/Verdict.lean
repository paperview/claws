-- The gate for the Game example. A human owns this file. Building it
-- fails unless every law in LAWS.lean, and every safety obligation in
-- Code.lean, has a complete proof.
import Claws
import Game.PROOF

#claws_verdict Game
