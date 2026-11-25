/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Compactification.RefinementPullback
public import WeilConjectures.Compactification.RefinementUniqueness
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Shriek
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Basic

/-!
# Compactly supported direct images in a compact support formalism

In a `AlgebraicGeometry.CompactSupportFormalism` `F`, a compactification `c = (X ⟶[i] Z ⟶[g] Y)`
of `f : X ⟶ Y` gives the compactly supported direct image `F.shriek c = i_! ⋙ g_*`. A refinement
`r : c.Refinement d` with cartesian square over `X` gives the comparison
`F.refinementComparison r : F.shriek d ⟶ F.shriek c`, built from the exchange map of the square
```
X --𝟙--> X
|c.i     |d.i
c.Z -r-> d.Z
```
It satisfies the identity and composition laws, and it is an isomorphism when `F` satisfies
proper base change. Comparing two compactifications through their common refinement gives
`F.shriekIso c d : F.shriek c ≅ F.shriek d`, which does not depend on the common refinement and
satisfies the cocycle condition (blueprint `proposition-construction-independence-rf-shriek`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TwoSquare

namespace AlgebraicGeometry.CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u})

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The compactly supported direct image `i_! ⋙ g_*` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)`: `CategoryTheory.ExchangeFormalism.shriek` of the factorization
`X ⟶[c.i] c.Z ⟶[c.g] Y`. -/
abbrev shriek (c : Compactification f) : F.obj X ⥤ F.obj Y := ExchangeFormalism.shriek F c.i c.g

section Refinement

variable [F.HasBaseChange] {c d e : Compactification f}

/-- **The comparison along a refinement** `r : c.Refinement d` whose square over `X` is
cartesian: the map `F.shriek d ⟶ F.shriek c` given by the exchange map
`(𝟙 X)_* ⋙ (d.i)_! ⟶ (c.i)_! ⋙ (r.hom)_*` followed by `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*`
(`CategoryTheory.ExchangeFormalism.refinementComparison`). -/
noncomputable def refinementComparison (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) : F.shriek d ⟶ F.shriek c :=
  haveI := HasBaseChange.isIso_baseChange (F := F) hr.flip
  ExchangeFormalism.refinementComparison F c.i c.g d.i d.g r.hom hr.flip.w r.hom_g

lemma refinementComparison_app (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : F.obj X) :
    haveI := HasBaseChange.isIso_baseChange (F := F) hr.flip
    (F.refinementComparison r hr).app K =
      (F.pf d.g).map ((F.sh d.i).map ((F.pfId X).inv.app K) ≫
          (F.exchange (𝟙 X) c.i d.i r.hom hr.flip.w).app K) ≫
        (F.pfComp' r.hom d.g c.g r.hom_g).inv.app ((F.sh c.i).obj K) :=
  haveI := HasBaseChange.isIso_baseChange (F := F) hr.flip
  ExchangeFormalism.refinementComparison_app F c.i c.g d.i d.g r.hom hr.flip.w r.hom_g K

/-- **The identity law**: the comparison along a refinement whose map is the identity is the
identity. -/
lemma refinementComparison_eq_id (r : c.Refinement c) (hr : IsPullback c.i (𝟙 X) r.hom c.i)
    (h : r.hom = 𝟙 c.Z) : F.refinementComparison r hr = 𝟙 _ := by
  obtain ⟨hom, i_hom, hom_g⟩ := r
  subst h
  have := HasBaseChange.isIso_baseChange (F := F) hr.flip
  exact ExchangeFormalism.refinementComparison_id F c.i c.g _ _

/-- **The composition law**: the comparison along a composite of refinements is the composite of
the comparisons, in the opposite order. -/
lemma refinementComparison_comp (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    F.refinementComparison (r.comp s) (Compactification.Refinement.isPullback_comp r s hr hs) =
      F.refinementComparison s hs ≫ F.refinementComparison r hr := by
  have hrs := Compactification.Refinement.isPullback_comp r s hr hs
  have := HasBaseChange.isIso_baseChange (F := F) hr.flip
  have := HasBaseChange.isIso_baseChange (F := F) hs.flip
  have := HasBaseChange.isIso_baseChange (F := F) hrs.flip
  exact ExchangeFormalism.refinementComparison_comp F c.i c.g d.i d.g e.i e.g r.hom s.hom _
    (Compactification.Refinement.comp_hom r s).symm _ _ _ _ _ _

/-- **The comparison along a refinement, through a base change isomorphism**: if the base change
map of the square of `r` is `β : c.i_! ≅ d.i_! ⋙ r^*` up to `(𝟙 X)^* ≅ 𝟭`, then the comparison
along `r` is the unit of `r^* ⊣ r_*`, followed by `β⁻¹` and by `r_* ⋙ (d.g)_* ≅ (c.g)_*`. -/
lemma refinementComparison_eq_of_baseChange (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (β : F.sh c.i ≅ F.sh d.i ⋙ F.pb r.hom)
    (hβ : (F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w) =
      Functor.whiskerRight (F.pbId X).hom (F.sh c.i) ≫ (Functor.leftUnitor _).hom ≫ β.hom) :
    F.refinementComparison r hr =
      Functor.whiskerRight (Functor.whiskerLeft (F.sh d.i) (F.adj r.hom).unit) (F.pf d.g) ≫
        Functor.whiskerRight β.inv (F.pf r.hom ⋙ F.pf d.g) ≫
        Functor.whiskerLeft (F.sh c.i) (F.pfComp' r.hom d.g c.g r.hom_g).inv :=
  haveI := HasBaseChange.isIso_baseChange (F := F) hr.flip
  ExchangeFormalism.refinementComparison_eq_of_baseChange F c.i c.g d.i d.g r.hom hr.flip.w
    r.hom_g β hβ

/-- The comparison along a refinement `r`, in terms of the unit of `r^* ⊣ r_*` and the inverse
of the base change map of the extension by zero of the square of `r`. -/
lemma refinementComparison_app_eq (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (K : F.obj X) :
    haveI := HasBaseChange.isIso_baseChange (F := F) hr.flip
    (F.refinementComparison r hr).app K =
      (F.pf d.g).map ((F.adj r.hom).unit.app ((F.sh d.i).obj K) ≫
        (F.pf r.hom).map (inv ((F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).app K) ≫
          (F.sh c.i).map ((F.pbId X).hom.app K))) ≫
        (F.pfComp' r.hom d.g c.g r.hom_g).inv.app ((F.sh c.i).obj K) :=
  haveI := HasBaseChange.isIso_baseChange (F := F) hr.flip
  ExchangeFormalism.refinementComparison_app_eq F c.i c.g d.i d.g r.hom hr.flip.w r.hom_g K

end Refinement


section ProperExchange

variable [F.HasProperExchange] {c d e : Compactification f}

instance isIso_refinementComparison (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) : IsIso (F.refinementComparison r hr) := by
  have := HasBaseChange.isIso_baseChange (F := F) hr.flip
  have := HasProperExchange.isIso_exchange (F := F) hr.flip
  unfold refinementComparison ExchangeFormalism.refinementComparison
  infer_instance

/-- Equal refinements give equal comparisons. -/
lemma asIso_refinementComparison_congr {r r' : c.Refinement d} (h : r = r')
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hr' : IsPullback c.i (𝟙 X) r'.hom d.i) :
    asIso (F.refinementComparison r hr) = asIso (F.refinementComparison r' hr') := by
  subst h
  rfl

lemma asIso_refinementComparison_comp (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    asIso (F.refinementComparison (r.comp s)
        (Compactification.Refinement.isPullback_comp r s hr hs)) =
      asIso (F.refinementComparison s hs) ≪≫ asIso (F.refinementComparison r hr) := by
  ext : 1
  exact F.refinementComparison_comp r s hr hs

/-- Comparing through a common refinement `e` gives the same isomorphism as comparing through
any further refinement of `e`. -/
lemma refinementComparison_trans_eq_of_refinement {c d e e' : Compactification f}
    (r : e.Refinement c) (s : e.Refinement d)
    (hr : IsPullback e.i (𝟙 X) r.hom c.i) (hs : IsPullback e.i (𝟙 X) s.hom d.i)
    (t : e'.Refinement e) (ht : IsPullback e'.i (𝟙 X) t.hom e.i) :
    asIso (F.refinementComparison r hr) ≪≫ (asIso (F.refinementComparison s hs)).symm =
      asIso (F.refinementComparison (t.comp r)
          (Compactification.Refinement.isPullback_comp t r ht hr)) ≪≫
        (asIso (F.refinementComparison (t.comp s)
          (Compactification.Refinement.isPullback_comp t s ht hs))).symm := by
  rw [F.asIso_refinementComparison_comp t r ht hr, F.asIso_refinementComparison_comp t s ht hs]
  ext : 1
  simp

variable [QuasiCompact f]

/-- **The comparison of two compactifications**: the isomorphism `F.shriek c ≅ F.shriek d`
obtained through the common refinement `Compactification.inf c d`. It does not depend on the
common refinement (`shriekIso_eq`) and satisfies the cocycle condition (`shriekIso_trans`); the
comparisons along refinements are the identity for identity refinements
(`refinementComparison_eq_id`) and transitive (`refinementComparison_comp`). This is the abstract
form of blueprint `proposition-construction-independence-rf-shriek`. -/
noncomputable def shriekIso (c d : Compactification f) : F.shriek c ≅ F.shriek d :=
  asIso (F.refinementComparison (Compactification.infFst c d)
      (Compactification.isPullback_infFst c d)) ≪≫
    (asIso (F.refinementComparison (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d))).symm

/-- **Independence of the common refinement**: comparing `c` and `d` through any common
refinement with cartesian squares over `X` gives `F.shriekIso c d`. -/
theorem shriekIso_eq (r : e.Refinement c) (s : e.Refinement d)
    (hr : IsPullback e.i (𝟙 X) r.hom c.i) (hs : IsPullback e.i (𝟙 X) s.hom d.i) :
    F.shriekIso c d =
      asIso (F.refinementComparison r hr) ≪≫ (asIso (F.refinementComparison s hs)).symm := by
  set e' := Compactification.inf c d
  have hdense := Compactification.isSchemeTheoreticallyDominant_inf_i e e'
  rw [shriekIso, F.refinementComparison_trans_eq_of_refinement r s hr hs
      (Compactification.infFst e e') (Compactification.isPullback_infFst e e'),
    F.refinementComparison_trans_eq_of_refinement _ _
      (Compactification.isPullback_infFst c d) (Compactification.isPullback_infSnd c d)
      (Compactification.infSnd e e') (Compactification.isPullback_infSnd e e'),
    F.asIso_refinementComparison_congr
      (Compactification.Refinement.ext_of_isSchemeTheoreticallyDominant hdense
        ((Compactification.infSnd e e').comp (Compactification.infFst c d))
        ((Compactification.infFst e e').comp r)),
    F.asIso_refinementComparison_congr
      (Compactification.Refinement.ext_of_isSchemeTheoreticallyDominant hdense
        ((Compactification.infSnd e e').comp (Compactification.infSnd c d))
        ((Compactification.infFst e e').comp s))]

/-- For a refinement `r : c.Refinement d` with cartesian square, `F.shriekIso c d` is the inverse
of the comparison along `r`. -/
theorem shriekIso_eq_symm (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    F.shriekIso c d = (asIso (F.refinementComparison r hr)).symm := by
  have hid : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i := by
    rw [Compactification.Refinement.id_hom]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  rw [F.shriekIso_eq (Compactification.Refinement.id c) r hid hr]
  ext : 1
  simp [F.refinementComparison_eq_id _ hid rfl]

@[simp]
theorem shriekIso_refl (c : Compactification f) : F.shriekIso c c = Iso.refl _ := by
  rw [F.shriekIso_eq (Compactification.infFst c c) (Compactification.infFst c c)
    (Compactification.isPullback_infFst c c) (Compactification.isPullback_infFst c c)]
  ext : 1
  simp

/-- **The cocycle condition.** -/
theorem shriekIso_trans (c₁ c₂ c₃ : Compactification f) :
    F.shriekIso c₁ c₂ ≪≫ F.shriekIso c₂ c₃ = F.shriekIso c₁ c₃ := by
  set e₁₂ := Compactification.inf c₁ c₂
  have h₁ := Compactification.Refinement.isPullback_comp (Compactification.infFst e₁₂ c₃)
    (Compactification.infFst c₁ c₂) (Compactification.isPullback_infFst e₁₂ c₃)
    (Compactification.isPullback_infFst c₁ c₂)
  have h₂ := Compactification.Refinement.isPullback_comp (Compactification.infFst e₁₂ c₃)
    (Compactification.infSnd c₁ c₂) (Compactification.isPullback_infFst e₁₂ c₃)
    (Compactification.isPullback_infSnd c₁ c₂)
  have h₃ := Compactification.isPullback_infSnd e₁₂ c₃
  rw [F.shriekIso_eq _ _ h₁ h₂, F.shriekIso_eq _ _ h₂ h₃, F.shriekIso_eq _ _ h₁ h₃]
  ext : 1
  simp

theorem shriekIso_symm (c d : Compactification f) :
    (F.shriekIso c d).symm = F.shriekIso d c := by
  have h := F.shriekIso_trans c d c
  rw [shriekIso_refl] at h
  ext : 1
  rw [Iso.symm_hom, ← cancel_epi (F.shriekIso c d).hom, Iso.hom_inv_id]
  exact (congrArg Iso.hom h).symm

end ProperExchange

end AlgebraicGeometry.CompactSupportFormalism
