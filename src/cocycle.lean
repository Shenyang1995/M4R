import M4R

variables (n:ℕ )(G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]

instance: add_comm_group (cochain n G M):=sorry

