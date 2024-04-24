def (a b : Ordinal) :
    a ^ b = if a = 0 then 1 - b else limitRecOn b 1 (fun _ IH => IH * a) fun b _ => bsup.{u, u} b :=
  rfl
#align ordinal.opow_def Ordinal.opow_def

def log (b : Ordinal) (x : Ordinal) : Ordinal :=
  if _h : 1 < b then pred (sInf { o | x < b ^ o }) else 0
#align ordinal.log Ordinal.log

def {b : Ordinal} (h : 1 < b) (x : Ordinal) : log b x = pred (sInf { o | x < b ^ o }) :=
  by simp only [log, dif_pos h]
#align ordinal.log_def Ordinal.log_def

def b1, ← Ordinal.le_zero, pred_le]
    apply csInf_le'
    dsimp
    rw [succ_zero, opow_one]
    exact zero_lt_one.trans b1
  else by simp only [log_of_not_one_lt_left b1]
#align ordinal.log_zero_right Ordinal.log_zero_right

def {b x : Ordinal} (hb : 1 < b) (hx : x ≠ 0) :
    succ (log b x) = sInf { o : Ordinal | x < b ^ o } := by
  let t := sInf { o : Ordinal | x < b ^ o }
  have : x < (b^t) := csInf_mem (log_nonempty hb)
  rcases zero_or_succ_or_limit t with (h | h | h)
  · refine' ((one_le_iff_ne_zero.2 hx).not_lt _).elim
    simpa only [h, opow_zero] using this
  · rw [show log b x = pred t from log_def hb x, succ_pred_iff_is_succ.2 h]
  · rcases (lt_opow_of_limit (zero_lt_one.trans hb).ne' h).1 this with ⟨a, h₁, h₂⟩
    exact h₁.not_le.elim ((le_csInf_iff'' (log_nonempty hb)).1 le_rfl a h₂)
#align ordinal.succ_log_def Ordinal.succ_log_def

def hb hx]
    exact csInf_mem (log_nonempty hb)
#align ordinal.lt_opow_succ_log_self Ordinal.lt_opow_succ_log_self

def hb hx] at this
  · rwa [one_opow, one_le_iff_ne_zero]
#align ordinal.opow_log_le_self Ordinal.opow_log_le_self

def hb h]
    apply csInf_le'
    apply mod_lt
    rw [← Ordinal.pos_iff_ne_zero]
    exact opow_pos _ (zero_lt_one.trans hb)
#align ordinal.log_mod_opow_log_lt_log_self Ordinal.log_mod_opow_log_lt_log_self

def positivity_opow : expr → tactic strictness
--   | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => positive <$> mk_app `` opow_pos [b, p]
--       | _ => failed
--   |-- We already know that `0 ≤ x` for all `x : Ordinal`
--     _ =>
--     failed
-- #align tactic.positivity_opow Tactic.positivity_opow