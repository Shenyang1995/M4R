import M4R

import algebra.pi_instances

variables (n:ℕ )(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]

instance: add_comm_group (cochain n G M):=
by unfold cochain; apply_instance

