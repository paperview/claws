-- The gate for the Vectors example. A human owns this file. Building it
-- fails unless every law in LAWS.lean, and every safety obligation in
-- Code.lean, has a complete proof.
import Claws
import Vectors.PROOF

#claws_verdict Vectors
