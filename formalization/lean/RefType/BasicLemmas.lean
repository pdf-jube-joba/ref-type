import RefType.Judgement

namespace RefType

theorem Derives.contextWF {Γ : Context} {J : Sequent} (h : Derives Γ J) : WF Γ := by
  induction h <;> first
    | assumption
    | exact Derives.wfEmpty
    | apply Derives.wfTmExtend <;> assumption
    | apply Derives.wfTyExtend <;> assumption

theorem HasSort.contextWF (h : HasSort Γ A s) : WF Γ :=
  Derives.contextWF h

theorem IsCarrier.contextWF (h : IsCarrier Γ C s) : WF Γ :=
  Derives.contextWF h

theorem HasType.contextWF (h : HasType Γ t A s) : WF Γ :=
  Derives.contextWF h

theorem Provable.contextWF (h : Provable Γ P) : WF Γ :=
  Derives.contextWF h

theorem wfTmCons_generation
    (h : WF ({ kind := .tm, sort := s, ty := A } :: Γ)) :
    WF Γ ∧ HasSort Γ A s := by
  cases h with
  | wfTmExtend hΓ hA => exact ⟨hΓ, hA⟩

theorem wfTyCons_generation
    (h : WF ({ kind := .ty, sort := s, ty := C } :: Γ)) :
    WF Γ ∧ IsCarrier Γ C s := by
  cases h with
  | wfTyExtend hΓ _ hC => exact ⟨hΓ, hC⟩

theorem wfTyCons_carrier_generation
    (h : WF ({ kind := .ty, sort := s, ty := C } :: Γ)) :
    ∃ carrierSort, HasSort Γ C carrierSort := by
  cases h with
  | wfTyExtend _ hC _ => exact ⟨_, hC⟩

theorem wfTail (h : WF (d :: Γ)) : WF Γ := by
  cases d with
  | mk kind sort ty =>
      cases kind with
      | tm => exact (wfTmCons_generation h).1
      | ty => exact (wfTyCons_generation h).1

theorem lookup_regular
    (hΓ : WF Γ) (h : Lookup Γ k i A s) :
    match k with
    | .tm => HasSort Γ A s
    | .ty => IsCarrier Γ A s := by
  induction h with
  | @here k _ _ _ =>
      cases k with
      | tm => exact Derives.sortWeak (wfTmCons_generation hΓ).2 hΓ
      | ty => exact Derives.carrierWeak (wfTyCons_generation hΓ).2 hΓ
  | @thereSame _ k _ _ _ _ _ _ ih =>
      cases k with
      | tm => exact Derives.sortWeak (ih (wfTail hΓ)) hΓ
      | ty => exact Derives.carrierWeak (ih (wfTail hΓ)) hΓ
  | @thereOther _ k _ _ _ _ _ _ _ _ ih =>
      cases k with
      | tm => exact Derives.sortWeak (ih (wfTail hΓ)) hΓ
      | ty => exact Derives.carrierWeak (ih (wfTail hΓ)) hΓ

theorem lookupTm_hasSort
    (hΓ : WF Γ) (h : Lookup Γ .tm i A s) : HasSort Γ A s :=
  lookup_regular hΓ h

theorem lookupTy_isCarrier
    (hΓ : WF Γ) (h : Lookup Γ .ty i C s) : IsCarrier Γ C s :=
  lookup_regular hΓ h

theorem tmVar_typeFormed
    (hΓ : WF Γ) (h : Lookup Γ .tm i A s) : HasSort Γ A s :=
  lookupTm_hasSort hΓ h

theorem tyVar_carrier
    (hΓ : WF Γ) (h : Lookup Γ .ty i C s) : IsCarrier Γ C s :=
  lookupTy_isCarrier hΓ h

end RefType
