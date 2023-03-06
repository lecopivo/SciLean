-- necessary operations 
abbrev ℝ := Float

def inverse (f : α → β) : β → α := sorry
postfix:max (priority:=high) " ⁻¹ " => inverse

def derivative (f : ℝ → ℝ) : ℝ → ℝ := sorry
macro (priority:=high) " ⅆ " "(" x:ident ":=" xval:term ")" "," fval:term : term => `((derivative λ $x => $fval) $xval )



-- internal energy -------------------------------------------------------------
def U (S : ℝ) (V : ℝ) : ℝ := sorry

-- definition of temperature and pressure as functions of entropy and volume
def T_sv (s v) := ⅆ (s':=s), U s' v
def P_sv (s v) := - ⅆ (v':=v), U s v'


theorem MaxwellRelation1 (s v) 
  : (ⅆ (v':=v), T_sv s v') = - (ⅆ (s':=s), P_sv s' v) :=
by
  unfold T_sv P_sv
  -- swap derivatives and we are done
  admit

-- Enthalpy --------------------------------------------------------------------

-- volume and temperature as functions of entropy and pressure
-- change of variables comming from Legandre transform
def V_sp (s p : ℝ) := (λ v => P_sv s v)⁻¹ p
def T_sp (s p : ℝ) := T_sv s (V_sp s p)

-- Enthalpy
-- H is leganre transform of U w.r.t. to V variable
def H (s p : ℝ) : ℝ := U s (T_sp s p) - p * T_sp s p

theorem enthalpy_temperature (s p) : T_sp s p = (ⅆ (s':=s), H s' p) := sorry
theorem enthalpy_volume      (s p) : V_sp s p = (ⅆ (p':=p), H s p') := sorry

theorem MaxwellRelation2 (s p) 
  : (ⅆ (p':=p), T_sp s p') = (ⅆ (s':=s), V_sp s' p) := 
by
  simp only [enthalpy_temperature, enthalpy_volume]
  -- swap derivatives and we are done
  admit


-- Helmholtz -------------------------------------------------------------------

-- entropy and pressure as functions of temperature and volume
def S_tv (t v : ℝ) := (λ s => T_sv s v)⁻¹ t
def P_tv (t v : ℝ) := P_sv (S_tv t v) v


-- Helmholtz free energy
-- F is leganre transform of U w.r.t. to S variable
def F (t v : ℝ) : ℝ := U (S_tv t v) v - t * S_tv t v

theorem helmholtz_pressure (t v : ℝ) : P_tv t v = - (ⅆ (v':=v), F t v') := sorry
theorem helmholtz_entropy  (t v : ℝ) : S_tv t v = - (ⅆ (t':=t), F t' v) := sorry

theorem MaxwellRelation3 (t v) 
  : (ⅆ (v':=v), S_tv t v') = (ⅆ (t':=t), P_tv t' v) :=
by
  simp only [helmholtz_pressure,helmholtz_entropy]
  -- swap derivatives and we are done
  admit
