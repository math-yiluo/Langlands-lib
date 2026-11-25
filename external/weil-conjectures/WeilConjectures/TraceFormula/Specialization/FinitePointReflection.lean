/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOverField
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.TraceFormula.OpenCover
public import WeilConjectures.TraceFormula.Specialization.ClosedPointsSupport
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFiniteness
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-!

# Reflection of bounded constructibility along a finite morphism to a separably closed point

Let `k` be a separably closed field and `p : Y ⟶ Spec k` a finite morphism, so that `Y` is a finite
discrete scheme whose residue fields `κ(x)` are finite, hence purely inseparable, over `k`, and
separably closed. A complex `K` of `Λ`-modules on `Y_proét` whose derived pushforward `Rp_* K` is
bounded constructible is itself bounded constructible
(`boundedConstructible_of_boundedConstructible_rightDerivedLowerStar_of_isFinite`).

The proof works with the points `x : Spec κ(x) ⟶ Y`, which are closed immersions:
* a module object `F` on `Y` is the direct sum `⨁ₓ x_* x^* F`
  (`ProEtale.CondensedRing.isIso_biproduct_lift_unit_app_fromSpecResidueField`), since the
  pullbacks to the points jointly reflect isomorphisms and `y^* x_* = 0` for `x ≠ y`; hence
  `(x ≫ p)_* x^* F` is a retract of `p_* F`;
* along the morphism `x ≫ p : Spec κ(x) ⟶ Spec k` of separably closed points the pullback is an
  equivalence (`ProEtale.CondensedRing.isEquivalence_upperStar_of_isField`), both categories being
  equivalent to condensed `Λ`-modules;
* a retract of a finitely presented module is finitely presented when the regular module is
  projective (`CategoryTheory.Mod.IsFinitelyPresented.of_retract`), as it is on `Spec k`.
So `p_*` is conservative and `F` is constructible (for the stratification by points) as soon as
`p_* F` is finitely presented; since `p_*` is exact, `Hⁿ(Rp_* K) ≅ p_* Hⁿ(K)`.

The equivalence of `Mod_{Spec Ω}` with condensed `Λ`-modules for separably closed `Ω` is
`ProEtale.CondensedRing.isEquivalence_upperStarFromPointMod`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]

/-- The finite free module `Rⁿ` is projective when the regular module is: a morphism out of
`Rⁿ` lifts summand by summand. -/
instance projective_finiteFree [Projective (regular R)] (n : ℕ) : Projective (finiteFree R n) :=
  ⟨fun f e _ ↦ ⟨biproduct.desc fun b ↦ Projective.factorThru
    (biproduct.ι (fun _ : Fin n ↦ regular R) b ≫ f) e, by
    refine biproduct.hom_ext' _ _ fun b ↦ ?_
    simp⟩⟩

/-- **A retract of a finitely presented module is finitely presented**, when the regular module
is projective. If `N = coker(f : Rᵐ ⟶ Rⁿ)` with projection `π : Rⁿ ⟶ N`, and `M` is a retract of
`N` through `s : M ⟶ N`, `r : N ⟶ M`, lift `π ≫ (𝟙 - r ≫ s)` along `π` to `h : Rⁿ ⟶ Rⁿ`; then
`M` is the cokernel of `(f, h) : Rᵐ⁺ⁿ ⟶ Rⁿ`, with projection `π ≫ r`. -/
theorem IsFinitelyPresented.of_retract [Projective (regular R)] {M N : Mod C R} (s : M ⟶ N)
    (r : N ⟶ M) (hsr : s ≫ r = 𝟙 M) (hN : IsFinitelyPresented R N) :
    IsFinitelyPresented R M := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hN
  let π : finiteFree R n ⟶ N := cokernel.π f ≫ e.inv
  have hπ : f ≫ π = 0 := by simp [π]
  have : Epi π := epi_comp _ _
  let h : finiteFree R n ⟶ finiteFree R n := Projective.factorThru (π ≫ (𝟙 N - r ≫ s)) π
  have hh : h ≫ π = π ≫ (𝟙 N - r ≫ s) := Projective.factorThru_comp _ _
  have hr : (𝟙 N - r ≫ s) ≫ r = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hsr]
    simp
  let g : finiteFree R (m + n) ⟶ finiteFree R n :=
    biproduct.desc (Fin.addCases (motive := fun _ ↦ regular R ⟶ finiteFree R n)
      (fun a ↦ biproduct.ι (fun _ : Fin m ↦ regular R) a ≫ f)
      (fun b ↦ biproduct.ι (fun _ : Fin n ↦ regular R) b ≫ h))
  have hg {T : Mod C R} (t : finiteFree R n ⟶ T) (ht : g ≫ t = 0) : f ≫ t = 0 ∧ h ≫ t = 0 := by
    constructor
    · refine biproduct.hom_ext' _ _ fun a ↦ ?_
      have := biproduct.ι _ (Fin.castAdd n a) ≫= ht
      simpa [g] using this
    · refine biproduct.hom_ext' _ _ fun b ↦ ?_
      have := biproduct.ι _ (Fin.natAdd m b) ≫= ht
      simpa [g] using this
  have hw : g ≫ π ≫ r = 0 := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i
    · simp [g, reassoc_of% hπ]
    · simp [g, reassoc_of% hh, hr]
  have h₁ {T : Mod C R} (t : finiteFree R n ⟶ T) (ht : g ≫ t = 0) :
      π ≫ e.hom ≫ cokernel.desc f t (hg t ht).1 = t := by
    simp [π]
  have h₃ {T : Mod C R} (t : finiteFree R n ⟶ T) (ht : g ≫ t = 0) :
      (π ≫ r) ≫ s ≫ e.hom ≫ cokernel.desc f t (hg t ht).1 = t := by
    have h₂ : π ≫ (𝟙 N - r ≫ s) ≫ e.hom ≫ cokernel.desc f t (hg t ht).1 = 0 := by
      rw [← reassoc_of% hh, h₁ t ht, (hg t ht).2]
    rw [Preadditive.sub_comp, Preadditive.comp_sub, sub_eq_zero, Category.id_comp,
      h₁ t ht] at h₂
    simpa using h₂.symm
  have : Epi (π ≫ r) := by
    have : Epi r := ⟨fun a b hab ↦ by simpa [reassoc_of% hsr] using s ≫= hab⟩
    exact epi_comp _ _
  let hc : IsColimit (CokernelCofork.ofπ (π ≫ r) hw) := CokernelCofork.IsColimit.ofπ _ hw
    (fun t ht ↦ s ≫ e.hom ≫ cokernel.desc f t (hg t ht).1) h₃
    (fun t ht m hm ↦ by rw [← cancel_epi (π ≫ r), hm, h₃ t ht])
  exact ⟨n, m + n, g, ⟨hc.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

end Mod
namespace Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A morphism `A ⟶ ⨁ B` into a biproduct is an isomorphism if its component at `j₀` is an
isomorphism and all the other factors `B j` are zero. -/
lemma isIso_biproduct_lift_of_isZero {J : Type*} {A : C} {B : J → C} [HasBiproduct B]
    (f : ∀ j, A ⟶ B j) (j₀ : J) [IsIso (f j₀)] (hB : ∀ j, j ≠ j₀ → IsZero (B j)) :
    IsIso (biproduct.lift f) := by
  refine ⟨biproduct.π B j₀ ≫ inv (f j₀), by simp, biproduct.hom_ext _ _ fun j ↦ ?_⟩
  by_cases hj : j = j₀
  · subst hj
    simp
  · exact (hB j hj).eq_of_tgt _ _

end Limits

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- For a separably closed field `R`, the pullback `Mod_Λ ⥤ Mod_{Spec R}` from condensed
`Λ`-modules is an equivalence (`ProEtale.CondensedRing.isEquivalence_upperStarFromPointMod`),
stated for the spectrum of a commutative ring which is a field. -/
lemma isEquivalence_upperStarFromPointMod_of_isField {R : CommRingCat.{u}} (hR : IsField R)
    (hsep : letI := hR.toField; IsSepClosed R) : (upperStarFromPointMod Λ (Spec R)).IsEquivalence :=
  letI := hR.toField
  isEquivalence_upperStarFromPointMod Λ (Ω := R)

/-- The pullback of `Λ`-modules along a morphism `g : Spec R ⟶ Spec R'` of separably closed
points is an equivalence: both `Mod_{Spec R}` and `Mod_{Spec R'}` are equivalent to condensed
`Λ`-modules through the pullbacks from the point, compatibly with `g^*`
(`ProEtale.CondensedRing.upperStarFromPointModComp`). -/
lemma isEquivalence_upperStar_of_isField {R R' : CommRingCat.{u}} (hR : IsField R)
    (hsep : letI := hR.toField; IsSepClosed R) (hR' : IsField R')
    (hsep' : letI := hR'.toField; IsSepClosed R') (g : Spec R ⟶ Spec R') :
    ((g)^*⟦Λ⟧).IsEquivalence := by
  have := isEquivalence_upperStarFromPointMod_of_isField Λ hR hsep
  have := isEquivalence_upperStarFromPointMod_of_isField Λ hR' hsep'
  have : (upperStarFromPointMod Λ (Spec R') ⋙ (g)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (upperStarFromPointModComp Λ g).symm
  exact Functor.isEquivalence_of_comp_left (upperStarFromPointMod Λ (Spec R')) _

/-- For a closed immersion `i`, the pullback `i^*` of the unit `F ⟶ i_* i^* F` is an
isomorphism: by the triangle identity it is inverse to the counit `i^* i_* i^* F ⟶ i^* F`, which
is an isomorphism. -/
lemma isIso_upperStar_map_unit_app_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso ((i)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ i).unit.app F)) :=
  @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ _ (IsIso.id _)
    ((upperStarLowerStarAdjunction Λ i).left_triangle_components F)

section Discrete

variable {Y : Scheme.{u}} [DiscreteTopology Y]

/-- On a discrete scheme, the pullback to a point `y` of the pushforward from another point
`x ≠ y` vanishes: the point `y` is open and misses the point `x`. -/
lemma isZero_upperStar_fromSpecResidueField_obj_lowerStar_obj {x y : Y} (hxy : x ≠ y)
    (G : Mod (Sheaf (Scheme.ProEt.topology (Spec (Y.residueField x))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (Y.residueField x)))) :
    IsZero ((Y.fromSpecResidueField y)^*⟦Λ⟧.obj ((Y.fromSpecResidueField x)_*⟦Λ⟧.obj G)) := by
  let U : Y.Opens := ⟨{y}, isOpen_discrete _⟩
  have hU : IsZero ((U.ι)^*⟦Λ⟧.obj ((Y.fromSpecResidueField x)_*⟦Λ⟧.obj G)) := by
    refine isZero_of_isZero_X Λ ((ProEtale.isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1}
      (Y.fromSpecResidueField x) U.ι ?_ G.X).of_iso (upperStarObjXIso Λ U.ι _))
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.disjoint_singleton.2 hxy
  have hy : Set.range (Y.fromSpecResidueField y) ⊆ Set.range U.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    rfl
  rw [← IsOpenImmersion.lift_fac U.ι (Y.fromSpecResidueField y) hy]
  exact ((IsOpenImmersion.lift U.ι _ hy)^*⟦Λ⟧.map_isZero hU).of_iso ((upperStarComp Λ _ _).app _)
variable [Finite Y]

/-- **A module object on a finite discrete scheme is the product of its pushforwards from the
points**: the units `F ⟶ x_* x^* F` along the points `x : Spec κ(x) ⟶ Y` assemble into an
isomorphism `F ≅ ⨁ₓ x_* x^* F`. The pullbacks to the points jointly reflect isomorphisms, and the
pullback to `y` of this map is `y^*` of the unit at `y`, an isomorphism, the other factors
vanishing. -/
lemma isIso_biproduct_lift_unit_app_fromSpecResidueField
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    IsIso (biproduct.lift fun x : Y ↦
      (upperStarLowerStarAdjunction Λ (Y.fromSpecResidueField x)).unit.app F) := by
  have (x : Y) : IsClosedImmersion (Y.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.1 (isClosed_discrete _)
  have h (y : Y) : IsIso ((Y.fromSpecResidueField y)^*⟦Λ⟧.map (biproduct.lift fun x : Y ↦
      (upperStarLowerStarAdjunction Λ (Y.fromSpecResidueField x)).unit.app F)) := by
    have := isIso_upperStar_map_unit_app_of_isClosedImmersion Λ (Y.fromSpecResidueField y) F
    have := isIso_biproduct_lift_of_isZero (fun x : Y ↦ (Y.fromSpecResidueField y)^*⟦Λ⟧.map
      ((upperStarLowerStarAdjunction Λ (Y.fromSpecResidueField x)).unit.app F)) y
      (fun x hx ↦ isZero_upperStar_fromSpecResidueField_obj_lowerStar_obj Λ hx _)
    exact IsIso.of_isIso_fac_right (biproduct.map_lift_mapBiprod _ _ _)
  exact (jointlyReflectIsomorphisms_upperStar_of_cover Λ (fun x : Y ↦ Y.fromSpecResidueField x)
    (fun x ↦ ⟨x, by simp [Scheme.range_fromSpecResidueField]⟩)).isIso _

/-- On a finite discrete scheme, the pushforward `x_* x^* F` from a point is a retract of `F`,
with retraction the unit `F ⟶ x_* x^* F`. -/
lemma exists_comp_unit_app_fromSpecResidueField_eq_id (x : Y)
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ∃ s : (Y.fromSpecResidueField x)_*⟦Λ⟧.obj ((Y.fromSpecResidueField x)^*⟦Λ⟧.obj F) ⟶ F,
      s ≫ (upperStarLowerStarAdjunction Λ (Y.fromSpecResidueField x)).unit.app F = 𝟙 _ := by
  let e := @asIso _ _ _ _ _ (isIso_biproduct_lift_unit_app_fromSpecResidueField Λ F)
  refine ⟨biproduct.ι (fun x : Y ↦ ((Y.fromSpecResidueField x)^*⟦Λ⟧ ⋙
    (Y.fromSpecResidueField x)_*⟦Λ⟧).obj F) x ≫ e.inv, ?_⟩
  have h : e.inv ≫ (upperStarLowerStarAdjunction Λ (Y.fromSpecResidueField x)).unit.app F =
      biproduct.π _ x := by
    rw [Iso.inv_comp_eq]
    simp [e]
  rw [Category.assoc, h]
  simp

open ZeroObject in
/-- On a finite discrete scheme, a module object whose pullbacks to all the points vanish is
zero: the pullbacks to the points jointly reflect isomorphisms, and they invert `F ⟶ 0`. -/
lemma isZero_of_forall_isZero_upperStar_fromSpecResidueField
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (h : ∀ x : Y, IsZero ((Y.fromSpecResidueField x)^*⟦Λ⟧.obj F)) : IsZero F := by
  have (x : Y) : IsClosedImmersion (Y.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.1 (isClosed_discrete _)
  have (x : Y) : IsIso ((Y.fromSpecResidueField x)^*⟦Λ⟧.map (0 : F ⟶ 0)) :=
    ⟨⟨0, (h x).eq_of_src _ _, ((Y.fromSpecResidueField x)^*⟦Λ⟧.map_isZero
      (isZero_zero _)).eq_of_src _ _⟩⟩
  have := (jointlyReflectIsomorphisms_upperStar_of_cover Λ
    (fun x : Y ↦ Y.fromSpecResidueField x)
    (fun x ↦ ⟨x, by simp [Scheme.range_fromSpecResidueField]⟩)).isIso (0 : F ⟶ 0)
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))


end Discrete
section FiniteOverPoint

variable {k : Type u} [Field k] [IsSepClosed k] {Y : Scheme.{u}}

omit [IsSepClosed k] in
/-- The points of a scheme finite over a field are closed. -/
lemma isClosedImmersion_fromSpecResidueField_of_isFinite (p : Y ⟶ Spec (.of k)) [IsFinite p]
    (x : Y) :
    IsClosedImmersion (Y.fromSpecResidueField x) :=
  have := (finite_and_discreteTopology_of_isFinite p).2
  isClosed_singleton_iff_isClosedImmersion.1 (isClosed_discrete _)

/-- The residue fields of a scheme finite over a separably closed field `k` are separably
closed: they are finite, hence purely inseparable, over `k`. -/
lemma isSepClosed_residueField_of_isFinite (p : Y ⟶ Spec (.of k)) [IsFinite p] (x : Y) :
    IsSepClosed (Y.residueField x) :=
  have := isClosedImmersion_fromSpecResidueField_of_isFinite p x
  isSepClosed_of_locallyOfFiniteType (Y.residueField x) (Y.fromSpecResidueField x ≫ p)

omit [IsSepClosed k] in
/-- For a scheme `Y` finite over `Spec k` and a point `x : Spec κ(x) ⟶ Y`, the pushforward
`(x ≫ p)_* x^* F` to `Spec k` is a retract of `p_* F`: apply `p_*` to the retraction
`F ⟶ x_* x^* F` (`exists_comp_unit_app_fromSpecResidueField_eq_id`). -/
lemma exists_retract_lowerStar_comp_fromSpecResidueField (p : Y ⟶ Spec (.of k)) [IsFinite p]
    (x : Y)
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ∃ (s : (Y.fromSpecResidueField x ≫ p)_*⟦Λ⟧.obj ((Y.fromSpecResidueField x)^*⟦Λ⟧.obj F) ⟶
      (p)_*⟦Λ⟧.obj F) (r : (p)_*⟦Λ⟧.obj F ⟶
        (Y.fromSpecResidueField x ≫ p)_*⟦Λ⟧.obj ((Y.fromSpecResidueField x)^*⟦Λ⟧.obj F)),
      s ≫ r = 𝟙 _ := by
  obtain ⟨_, _⟩ := finite_and_discreteTopology_of_isFinite p
  obtain ⟨s, hs⟩ := exists_comp_unit_app_fromSpecResidueField_eq_id Λ x F
  let e := (lowerStarComp Λ (Y.fromSpecResidueField x) p).app
    ((Y.fromSpecResidueField x)^*⟦Λ⟧.obj F)
  refine ⟨e.inv ≫ (p)_*⟦Λ⟧.map s,
    (p)_*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ (Y.fromSpecResidueField x)).unit.app F) ≫
      e.hom, ?_⟩
  simp [← Functor.map_comp_assoc, hs]

/-- **Finite pushforward to a separably closed point is conservative**: for `p : Y ⟶ Spec k`
finite with `k` separably closed, a module object `F` on `Y` with `p_* F = 0` vanishes. At each
point `x` of the finite discrete scheme `Y`, `(x ≫ p)_* x^* F` is a retract of `p_* F`, and the
pushforward along `x ≫ p : Spec κ(x) ⟶ Spec k`, a morphism of separably closed points, is an
equivalence. -/
theorem isZero_of_isZero_lowerStar_of_isFinite_of_isSepClosed (p : Y ⟶ Spec (.of k)) [IsFinite p]
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hF : IsZero ((p)_*⟦Λ⟧.obj F)) : IsZero F := by
  obtain ⟨_, _⟩ := finite_and_discreteTopology_of_isFinite p
  refine isZero_of_forall_isZero_upperStar_fromSpecResidueField Λ F fun x ↦ ?_
  obtain ⟨s, r, hsr⟩ := exists_retract_lowerStar_comp_fromSpecResidueField Λ p x F
  have hN : IsZero ((Y.fromSpecResidueField x ≫ p)_*⟦Λ⟧.obj
      ((Y.fromSpecResidueField x)^*⟦Λ⟧.obj F)) :=
    (IsZero.iff_id_eq_zero _).2 (by rw [← hsr, hF.eq_of_src r 0, comp_zero])
  have := isSepClosed_residueField_of_isFinite p x
  have := isEquivalence_upperStar_of_isField Λ (Field.toIsField (Y.residueField x))
    IsField.isSepClosed_toField (Field.toIsField k) IsField.isSepClosed_toField
    (Y.fromSpecResidueField x ≫ p)
  exact ((Y.fromSpecResidueField x ≫ p)^*⟦Λ⟧.map_isZero hN).of_iso
    (asIso ((upperStarLowerStarAdjunction Λ _).counit.app _)).symm

/-- For `p : Y ⟶ Spec k` finite with `k` separably closed, if `p_* F` is finitely presented, so
is the pullback `x^* F` of `F` to each point `x : Spec κ(x) ⟶ Y`: the pushforward
`(x ≫ p)_* x^* F` is a retract of `p_* F`, hence finitely presented (the regular module on
`Spec k` being projective), and `(x ≫ p)^*` is an equivalence. -/
theorem isFinitelyPresented_upperStar_fromSpecResidueField_of_isFinite (p : Y ⟶ Spec (.of k))
    [IsFinite p]
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hF : Mod.IsFinitelyPresented _ ((p)_*⟦Λ⟧.obj F)) (x : Y) :
    Mod.IsFinitelyPresented _ ((Y.fromSpecResidueField x)^*⟦Λ⟧.obj F) := by
  obtain ⟨s, r, hsr⟩ := exists_retract_lowerStar_comp_fromSpecResidueField Λ p x F
  have hN := Mod.IsFinitelyPresented.of_retract s r hsr hF
  have := isSepClosed_residueField_of_isFinite p x
  have := isEquivalence_upperStar_of_isField Λ (Field.toIsField (Y.residueField x))
    IsField.isSepClosed_toField (Field.toIsField k) IsField.isSepClosed_toField
    (Y.fromSpecResidueField x ≫ p)
  exact (IsFinitelyPresented.upperStar Λ _ hN).of_iso
    (asIso ((upperStarLowerStarAdjunction Λ _).counit.app _))
/-- For `p : Y ⟶ Spec k` finite with `k` separably closed, a module object `F` on `Y` whose
pushforward `p_* F` is finitely presented is constructible, for the stratification of the finite
discrete scheme `Y` by its points: the pullbacks to the points are finitely presented
(`isFinitelyPresented_upperStar_fromSpecResidueField_of_isFinite`). -/
theorem isConstructibleModuleObject_of_isFinitelyPresented_lowerStar (p : Y ⟶ Spec (.of k))
    [IsFinite p] (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hF : Mod.IsFinitelyPresented _ ((p)_*⟦Λ⟧.obj F)) :
    IsConstructibleModuleObject (condensedRingObj Λ Y) F := by
  obtain ⟨_, _⟩ := finite_and_discreteTopology_of_isFinite p
  have := isClosedImmersion_fromSpecResidueField_of_isFinite p
  obtain ⟨e⟩ : Nonempty (Fin (Nat.card Y) ≃ Y) := ⟨(Finite.equivFin Y).symm⟩
  refine ⟨{ n := Nat.card Y
            stratum := fun i ↦ {e i}
            isLocallyClosed_stratum := fun i ↦ (isClosed_discrete _).isLocallyClosed
            isConstructible_stratum := fun i ↦
              (isClosed_discrete _).isLocallyClosed.isConstructible_of_noetherianSpace
            iUnion_stratum_eq_univ :=
              Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨e.symm y, by simp⟩
            pairwise_disjoint_stratum := fun i j hij ↦
              Set.disjoint_singleton.2 (e.injective.ne hij)
            domain := fun i ↦ Spec (Y.residueField (e i))
            immersion := fun i ↦ Y.fromSpecResidueField (e i)
            range_immersion := fun i ↦ Scheme.range_fromSpecResidueField _ }, fun i ↦ ?_⟩
  exact (isLocallyFinitelyPresented_mapMod_iff Λ (Y.fromSpecResidueField (e i)) F).2
    (isLocallyFinitelyPresented_of_isFinitelyPresented Λ
      (isFinitelyPresented_upperStar_fromSpecResidueField_of_isFinite Λ p F hF (e i)))

/-- A constructible module object on a separably closed point `Spec k` is finitely presented
(`ProEtale.CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject` for the
identity point). -/
lemma isFinitelyPresented_of_isConstructibleModuleObject_of_isSepClosed
    {M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k)))}
    (hM : IsConstructibleModuleObject (condensedRingObj Λ (Spec (.of k))) M) :
    Mod.IsFinitelyPresented (condensedRingObj Λ (Spec (.of k))) M :=
  (isFinitelyPresented_upperStar_of_isConstructibleModuleObject Λ (Field.toIsField k)
    IsField.isSepClosed_toField hM (𝟙 _)).of_iso ((upperStarId Λ _).app M)

open scoped CategoryTheory.Functor in
/-- **Reflection of bounded constructibility along a finite morphism to a separably closed
point**: for `p : Y ⟶ Spec k` finite with `k` separably closed, a complex `K` on `Y` whose
derived pushforward `Rp_* K` is bounded constructible is bounded constructible. The pushforward
`p_*` is exact, so `Hⁿ(Rp_* K) ≅ p_* Hⁿ(K)`; it is conservative
(`isZero_of_isZero_lowerStar_of_isFinite_of_isSepClosed`), and `Hⁿ(K)` is constructible as soon
as `p_* Hⁿ(K)` is (`isConstructibleModuleObject_of_isFinitelyPresented_lowerStar`). -/
theorem boundedConstructible_of_boundedConstructible_rightDerivedLowerStar_of_isFinite
    (p : Y ⟶ Spec (.of k)) [IsFinite p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hK : boundedConstructible (condensedRingObj Λ (Spec (.of k))) ((R((p)_*⟦Λ⟧)).obj K)) :
    boundedConstructible (condensedRingObj Λ Y) K := by
  have : LocallyOfFinitePresentation p :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have := preservesFiniteColimits_lowerStar_of_isFinite Λ p
  let ρ (n : ℤ) := ((p)_*⟦Λ⟧.rightDerivedFunctorHomologyFunctorIso n).app K
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ _).1 hK
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact isZero_of_isZero_lowerStar_of_isFinite_of_isSepClosed Λ p _ ((hab i hi).of_iso (ρ i))
  · exact isConstructibleModuleObject_of_isFinitelyPresented_lowerStar Λ p _
      ((isFinitelyPresented_of_isConstructibleModuleObject_of_isSepClosed Λ (hc n)).of_iso
        (ρ n).symm)

end FiniteOverPoint

end AlgebraicGeometry.ProEtale.CondensedRing
