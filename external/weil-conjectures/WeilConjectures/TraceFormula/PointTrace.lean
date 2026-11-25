/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FieldDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TraceShiftUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.BraidedTrace
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.TraceShiftDecomposition
public import WeilConjectures.LinearAlgebra.TraceLongExactSequence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift
public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.TraceFormula.PointFiberFunctor

/-!
# Traces on the point category over a separably closed field

Let `k` be a separably closed field and `s = Spec k`. Evaluation at the geometric point identifies
the bounded constructible derived category `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` with the bounded derived category of
finite-dimensional `ℚ̄_ℓ`-vector spaces (blueprint `lemma-perfect-complexes-geometric-point`,
`ProEtale.CondensedRing.exists_fiberFunctor_point`). Consequently every object of
`Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is a finite direct sum of shifts of the unit.

This file shows that the categorical trace on `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is the supertrace on the graded
spaces `Hⁿ(P) = Hom(𝟙⟦n⟧, P)`, and deduces that the trace is additive along every endomorphism of
a distinguished triangle (blueprint `proposition-properties-trace`, items (2) and (4)): over a field
the filtered origin of the endomorphism is not needed.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] boundedConstructibleBraiding

example : MonoidalPreadditive (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  inferInstance

example (n : ℤ) :
    (shiftFunctor (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) n).Additive :=
  inferInstance


end AlgebraicGeometry.ProEtale.CondensedRing

namespace DerivedCategory

variable {F : Type (u + 1)} [Field F]

/-- A retract of a bounded complex with finite-dimensional cohomology is again bounded with
finite-dimensional cohomology. -/
lemma boundedFiniteCohomology_of_retract {X Y : DerivedCategory (ModuleCat.{u + 1} F)}
    (i : X ⟶ Y) (p : Y ⟶ X) (h : i ≫ p = 𝟙 X) (hY : boundedFiniteCohomology F Y) :
    boundedFiniteCohomology F X := by
  have hz (n : ℤ) (hn : IsZero ((homologyFunctor _ n).obj Y)) :
      IsZero ((homologyFunctor _ n).obj X) := by
    rw [IsZero.iff_id_eq_zero, ← (homologyFunctor _ n).map_id, ← h, Functor.map_comp,
      hn.eq_of_tgt ((homologyFunctor _ n).map i) 0, zero_comp]
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hfin⟩ := hY
  refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun n ↦ ?_⟩
  · have ha' := (isGE_iff Y a).1 ha
    exact (isGE_iff X a).2 fun n hn ↦ hz n (ha' n hn)
  · have hb' := (isLE_iff Y b).1 hb
    exact (isLE_iff X b).2 fun n hn ↦ hz n (hb' n hn)
  · have := hfin n
    refine Module.Finite.of_surjective ((homologyFunctor _ n).map p).hom fun x ↦
      ⟨((homologyFunctor _ n).map i).hom x, ?_⟩
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, h, CategoryTheory.Functor.map_id]
    rfl

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] boundedConstructibleBraiding

/-- Over a separably closed field, every object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is a finite direct sum of
shifts of the unit: transported along the fibre functor of `exists_fiberFunctor_point`, this is
the splitting of bounded complexes of vector spaces
(`DerivedCategory.prop_of_boundedFiniteCohomology_of_field`). -/
theorem nonempty_shiftDecomposition_point
    (P : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (ShiftDecomposition (𝟙_ _) P) := by
  obtain ⟨G, _, hadd, ⟨hG⟩, hbfc, hess, ⟨e₀⟩⟩ := exists_fiberFunctor_point ℓ k
  have : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  let F := ULift.{u + 1} (PadicAlgCl ℓ)
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} F)) := fun Y ↦
    DerivedCategory.boundedFiniteCohomology F Y →
      ∀ P, (G.obj P ≅ Y) → Nonempty (ShiftDecomposition (𝟙_ _) P)
  have : Q.IsClosedUnderIsomorphisms := ⟨fun {Y Y'} e hY hY' P e' ↦
    hY ((DerivedCategory.boundedFiniteCohomology F).prop_of_iso e.symm hY') P (e' ≪≫ e.symm)⟩
  refine DerivedCategory.prop_of_boundedFiniteCohomology_of_field Q ?_ ?_ ?_ ?_ (hbfc P) (hbfc P)
    P (Iso.refl _)
  · intro Y hY _ P e
    refine ⟨ShiftDecomposition.ofIsZero ?_⟩
    rw [IsZero.iff_id_eq_zero]
    exact hG.map_injective (by rw [G.map_id, G.map_zero]; exact (hY.of_iso e).eq_of_src _ _)
  · intro X Y hX hY hXY P e
    have hX' := DerivedCategory.boundedFiniteCohomology_of_retract biprod.inl biprod.fst
      biprod.inl_fst hXY
    have hY' := DerivedCategory.boundedFiniteCohomology_of_retract biprod.inr biprod.snd
      biprod.inr_snd hXY
    obtain ⟨PX, ⟨eX⟩⟩ := hess X hX'
    obtain ⟨PY, ⟨eY⟩⟩ := hess Y hY'
    obtain ⟨DX⟩ := hX hX' PX eX
    obtain ⟨DY⟩ := hY hY' PY eY
    refine ⟨DX.sum DY (hG.preimage (eX.hom ≫ biprod.inl ≫ e.inv))
      (hG.preimage (eY.hom ≫ biprod.inr ≫ e.inv)) (hG.preimage (e.hom ≫ biprod.fst ≫ eX.inv))
      (hG.preimage (e.hom ≫ biprod.snd ≫ eY.inv)) ?_ ?_ ?_ ?_ ?_⟩
    · apply hG.map_injective
      simp only [G.map_add, G.map_comp, hG.map_preimage, Category.assoc, Iso.inv_hom_id_assoc,
        G.map_id]
      rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
      ← Preadditive.add_comp, biprod.total, Category.id_comp, Iso.hom_inv_id]
    all_goals
      apply hG.map_injective
      simp only [G.map_comp, hG.map_preimage, Category.assoc, Iso.inv_hom_id_assoc,
        G.map_id, G.map_zero, biprod.inl_fst_assoc, biprod.inr_snd_assoc, biprod.inl_snd_assoc,
        biprod.inr_fst_assoc, Iso.hom_inv_id, zero_comp, comp_zero]
  · intro X n hX hXn P e
    let P' := (shiftFunctor _ (-n)).obj P
    let e' : G.obj P' ≅ X := (G.commShiftIso (-n)).app P ≪≫ (shiftFunctor _ (-n)).mapIso e ≪≫
      (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).app X
    obtain ⟨D⟩ := hX ((DerivedCategory.boundedFiniteCohomology F).prop_of_iso e' (hbfc P')) P' e'
    exact ⟨(D.shift n).ofIso ((shiftFunctorCompIsoId _ (-n) n (neg_add_cancel n)).app P)⟩
  · intro _ P e
    exact ⟨(ShiftDecomposition.self _).ofIso (hG.preimageIso (e₀ ≪≫ e.symm))⟩

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Ambient

/-- The shifted unit `𝟙⟦n⟧` of `D(Mod_{ℚ̲̄_ℓ,s})`. -/
noncomputable abbrev shiftedUnit (n : ℤ) : DerivedCategory (PointMod ℓ k) :=
  (shiftFunctor (DerivedCategory (PointMod ℓ k)) n).obj (𝟙_ _)

/-- The scalars `ℚ̄_ℓ` acting on the unit of `D(Mod_{ℚ̲̄_ℓ,s})`. -/
noncomputable def pointScalar : PadicAlgCl ℓ →+* End (𝟙_ (DerivedCategory (PointMod ℓ k))) :=
  ((boundedConstructible _).ι.mapEndRingHom
    (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧))).comp
    (padicAlgClUnitEndRingHom ℓ (point k))

omit [Fact (ringChar k).Prime] in
lemma bijective_pointScalar [IsSepClosed k] : Function.Bijective (pointScalar ℓ k) :=
  (((ObjectProperty.fullyFaithfulι _).mulEquivEnd _).bijective).comp
    (bijective_padicAlgClUnitEndRingHom_point ℓ k)

/-- The scalars acting on the shifted unit `𝟙⟦n⟧` by precomposition. -/
noncomputable def shiftedUnitScalar (n : ℤ) :
    PadicAlgCl ℓ →+* (End (shiftedUnit ℓ k n))ᵐᵒᵖ :=
  (((shiftFunctor (DerivedCategory (PointMod ℓ k)) n).mapEndRingHom _).comp
    (pointScalar ℓ k)).toOpposite fun x y ↦ by
      unfold Commute SemiconjBy
      rw [← map_mul, mul_comm, map_mul]

/-- The graded pieces `Hⁿ(Y) = Hom(𝟙⟦n⟧, Y)` of `Y ∈ D(Mod_{ℚ̲̄_ℓ,s})`, as `ℚ̄_ℓ`-vector
spaces. -/
noncomputable def gradedHom (n : ℤ) : DerivedCategory (PointMod ℓ k) ⥤ ModuleCat (PadicAlgCl ℓ) :=
  preadditiveCoyonedaObj (shiftedUnit ℓ k n) ⋙
    ModuleCat.restrictScalars (shiftedUnitScalar ℓ k n)

instance (n : ℤ) : (gradedHom ℓ k n).Additive := by
  unfold gradedHom
  infer_instance


/-- A morphism `𝟙⟦n⟧ ⟶ Y` as an element of `Hⁿ(Y)`. -/
noncomputable def gradedHomMk {n : ℤ} {Y : DerivedCategory (PointMod ℓ k)}
    (x : shiftedUnit ℓ k n ⟶ Y) : (gradedHom ℓ k n).obj Y :=
  x

/-- An element of `Hⁿ(Y)` as a morphism `𝟙⟦n⟧ ⟶ Y`. -/
noncomputable def gradedHomHom {n : ℤ} {Y : DerivedCategory (PointMod ℓ k)}
    (x : (gradedHom ℓ k n).obj Y) : shiftedUnit ℓ k n ⟶ Y :=
  x

omit [Fact (ringChar k).Prime] in
lemma gradedHomHom_smul (n : ℤ) (Y : DerivedCategory (PointMod ℓ k)) (c : PadicAlgCl ℓ)
    (x : (gradedHom ℓ k n).obj Y) :
    gradedHomHom ℓ k (c • x) =
      (shiftFunctor (DerivedCategory (PointMod ℓ k)) n).map (pointScalar ℓ k c).asHom ≫
        gradedHomHom ℓ k x :=
  rfl

omit [Fact (ringChar k).Prime] in
lemma gradedHomHom_map_apply (n : ℤ) {Y Y' : DerivedCategory (PointMod ℓ k)} (f : Y ⟶ Y')
    (x : (gradedHom ℓ k n).obj Y) :
    gradedHomHom ℓ k (((gradedHom ℓ k n).map f).hom x) = gradedHomHom ℓ k x ≫ f :=
  rfl

end Ambient

end AlgebraicGeometry.ProEtale.CondensedRing

namespace DerivedCategory

variable {F : Type (u + 1)} [Field F]

/-- Morphisms `M[-b] ⟶ Z` vanish when `Hᵇ(Z) = 0`, over a field. -/
lemma eq_zero_of_singleFunctor_of_field (b : ℤ) (M : ModuleCat.{u + 1} F)
    (Z : DerivedCategory (ModuleCat.{u + 1} F))
    (hZ : IsZero ((homologyFunctor (ModuleCat.{u + 1} F) b).obj Z))
    (g : (singleFunctor (ModuleCat.{u + 1} F) b).obj M ⟶ Z) : g = 0 := by
  have : Projective M := inferInstanceAs (Projective (ModuleCat.of F M))
  apply (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) b).map_injective
  rw [Functor.map_zero, ← cancel_epi
    (((singleFunctors (ModuleCat.{u + 1} F)).shiftIso b 0 b (by lia)).inv.app M), Limits.comp_zero]
  refine eq_zero_of_isZero_homology_zero M _ ?_ _
  exact hZ.of_iso (((homologyFunctor (ModuleCat.{u + 1} F) 0).shiftIso b 0 b (by lia)).app Z)

/-- Over a field, there are no nonzero morphisms between distinct shifts of `F[0]`. -/
lemma subsingleton_hom_shift_singleFunctor (a b : ℤ) (hab : a ≠ b) :
    Subsingleton ((shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) a).obj
        ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F)) ⟶
      (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) b).obj
        ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F))) := by
  refine ⟨fun φ ψ ↦ ?_⟩
  suffices h : ∀ φ : (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) a).obj
      ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F)) ⟶
      (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) b).obj
        ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F)), φ = 0 by
    rw [h φ, h ψ]
  intro φ
  rw [← cancel_epi (((singleFunctors (ModuleCat.{u + 1} F)).shiftIso a (-a) 0 (by lia)).inv.app
    (ModuleCat.of F F)), Limits.comp_zero]
  refine eq_zero_of_singleFunctor_of_field (-a) _ _ ?_ _
  refine IsZero.of_iso ?_ (((homologyFunctor (ModuleCat.{u + 1} F) 0).shiftIso b (-a)
    (b - a) (by lia)).app _)
  rcases lt_or_gt_of_ne (sub_ne_zero.2 hab.symm) with h | h
  · exact isZero_of_isGE _ 0 _ h
  · exact isZero_of_isLE _ 0 _ h

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] boundedConstructibleBraiding

/-- There are no nonzero morphisms between distinct shifts of the unit of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`. -/
lemma subsingleton_hom_shift_unit_point (a b : ℤ) (hab : a ≠ b) :
    Subsingleton ((shiftFunctor (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) a).obj
        (𝟙_ _) ⟶
      (shiftFunctor (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) b).obj (𝟙_ _)) := by
  obtain ⟨G, _, _, ⟨hG⟩, -, -, ⟨e₀⟩⟩ := exists_fiberFunctor_point ℓ k
  have := DerivedCategory.subsingleton_hom_shift_singleFunctor
    (F := ULift.{u + 1} (PadicAlgCl ℓ)) a b hab
  exact (hG.homEquiv.trans (Iso.homCongr ((G.commShiftIso a).app _ ≪≫
    (shiftFunctor _ a).mapIso e₀) ((G.commShiftIso b).app _ ≪≫
      (shiftFunctor _ b).mapIso e₀))).subsingleton

/-- There are no nonzero morphisms between distinct shifts of the unit of `D(Mod_{ℚ̲̄_ℓ,s})`. -/
lemma subsingleton_hom_shiftedUnit (a b : ℤ) (hab : a ≠ b) :
    Subsingleton (shiftedUnit ℓ k a ⟶ shiftedUnit ℓ k b) := by
  have := subsingleton_hom_shift_unit_point ℓ k a b hab
  exact ((ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj
    (Profinite.padicAlgClRingObj ℓ) (point k).left))).homEquiv.trans
    (Iso.homCongr (((boundedConstructible _).ι.commShiftIso a).app (𝟙_ _))
      (((boundedConstructible _).ι.commShiftIso b).app (𝟙_ _)))).symm.subsingleton

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section GradedHom

/-- The scalars `ℚ̄_ℓ` are the endomorphisms of a shifted unit `𝟙⟦n⟧`: `c ↦ c • 𝟙`. -/
noncomputable def shiftedUnitEquiv (n : ℤ) :
    PadicAlgCl ℓ ≃ₗ[PadicAlgCl ℓ] (gradedHom ℓ k n).obj (shiftedUnit ℓ k n) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (gradedHomMk ℓ k (𝟙 _))) (by
    constructor
    · intro c d h
      have h' := congrArg (gradedHomHom ℓ k) h
      simp only [LinearMap.toSpanSingleton_apply, gradedHomHom_smul] at h'
      change (shiftFunctor _ n).map (pointScalar ℓ k c).asHom ≫ 𝟙 _ =
        (shiftFunctor _ n).map (pointScalar ℓ k d).asHom ≫ 𝟙 _ at h'
      rw [Category.comp_id, Category.comp_id] at h'
      exact (bijective_pointScalar ℓ k).1 (End.ext ((shiftFunctor _ n).map_injective h'))
    · intro x
      obtain ⟨c, hc⟩ := (End.homEquiv.bijective.comp (bijective_pointScalar ℓ k)).2
        ((shiftFunctor (DerivedCategory (PointMod ℓ k)) n).preimage (gradedHomHom ℓ k x))
      change (pointScalar ℓ k c).asHom = _ at hc
      refine ⟨c, ?_⟩
      change gradedHomHom ℓ k (c • gradedHomMk ℓ k (𝟙 _)) = gradedHomHom ℓ k x
      rw [gradedHomHom_smul]
      change (shiftFunctor _ n).map (pointScalar ℓ k c).asHom ≫ 𝟙 _ = _
      rw [Category.comp_id, hc, Functor.map_preimage])

omit [Fact (ringChar k).Prime] in
lemma gradedHomHom_shiftedUnitEquiv (n : ℤ) (c : PadicAlgCl ℓ) :
    gradedHomHom ℓ k (shiftedUnitEquiv ℓ k n c) =
      (shiftFunctor (DerivedCategory (PointMod ℓ k)) n).map (pointScalar ℓ k c).asHom := by
  change gradedHomHom ℓ k (c • gradedHomMk ℓ k (𝟙 _)) = _
  rw [gradedHomHom_smul]
  exact Category.comp_id _

instance finiteDimensional_gradedHom_shiftedUnit (n m : ℤ) :
    FiniteDimensional (PadicAlgCl ℓ) ((gradedHom ℓ k n).obj (shiftedUnit ℓ k m)) := by
  by_cases h : n = m
  · subst h
    exact Module.Finite.equiv (shiftedUnitEquiv ℓ k n)
  · have := subsingleton_hom_shiftedUnit ℓ k n m h
    have : Subsingleton ((gradedHom ℓ k n).obj (shiftedUnit ℓ k m)) :=
      inferInstanceAs (Subsingleton (shiftedUnit ℓ k n ⟶ shiftedUnit ℓ k m))
    infer_instance

/-- The induced action on `Hⁿ(𝟙⟦m⟧)` of the endomorphism `c • 𝟙` of `𝟙⟦m⟧` has trace `c` if
`n = m`, and `0` otherwise. -/
lemma linearMapTrace_gradedHom_map_shiftedUnitEquiv (n m : ℤ) (c : PadicAlgCl ℓ) :
    LinearMap.trace (PadicAlgCl ℓ) _ ((gradedHom ℓ k n).map
      (gradedHomHom ℓ k (shiftedUnitEquiv ℓ k m c))).hom = if n = m then c else 0 := by
  split_ifs with h
  · subst h
    have e : ((gradedHom ℓ k n).map (gradedHomHom ℓ k (shiftedUnitEquiv ℓ k n c))).hom =
        c • LinearMap.id := by
      ext x
      obtain ⟨d, rfl⟩ := (shiftedUnitEquiv ℓ k n).surjective x
      rw [LinearMap.smul_apply, LinearMap.id_apply, ← map_smul, smul_eq_mul]
      change gradedHomHom ℓ k (((gradedHom ℓ k n).map _).hom (shiftedUnitEquiv ℓ k n d)) =
        gradedHomHom ℓ k (shiftedUnitEquiv ℓ k n (c * d))
      rw [gradedHomHom_map_apply, gradedHomHom_shiftedUnitEquiv, gradedHomHom_shiftedUnitEquiv,
        gradedHomHom_shiftedUnitEquiv, ← Functor.map_comp, ← End.mul_asHom, ← map_mul]
    rw [e, map_smul, LinearMap.trace_id, ← (shiftedUnitEquiv ℓ k n).finrank_eq,
      Module.finrank_self, Nat.cast_one, smul_eq_mul, mul_one]
  · have := subsingleton_hom_shiftedUnit ℓ k n m h
    have : Subsingleton ((gradedHom ℓ k n).obj (shiftedUnit ℓ k m)) :=
      inferInstanceAs (Subsingleton (shiftedUnit ℓ k n ⟶ shiftedUnit ℓ k m))
    exact LinearMap.trace_eq_zero_of_subsingleton _

end GradedHom

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section TraceFormula

attribute [local instance] DerivedCategory.braidedCategory'

/-- A right dual of the shifted unit `𝟙⟦n⟧` of `D(Mod_{ℚ̲̄_ℓ,s})`. -/
noncomputable instance shiftedUnitHasRightDual (n : ℤ) : HasRightDual (shiftedUnit ℓ k n) :=
  (DerivedCategory.isDualizable_shift isDualizable_unit n).some

omit [Fact (ringChar k).Prime] in
/-- The trace of `c • 𝟙` on `𝟙⟦m⟧` is `(-1)ᵐ c`. -/
lemma trace_gradedHomHom_shiftedUnitEquiv (m : ℤ) (c : PadicAlgCl ℓ) :
    trace (gradedHomHom ℓ k (shiftedUnitEquiv ℓ k m c)) =
      (m.negOnePow : ℤ) • (pointScalar ℓ k c).asHom := by
  rw [gradedHomHom_shiftedUnitEquiv]
  let e : 𝟙_ (DerivedCategory (PointMod ℓ k)) ≅
      (DerivedCategory.singleFunctor (PointMod ℓ k) 0).obj (𝟙_ _) :=
    (DerivedCategory.quotientCompQhIso (PointMod ℓ k)).app (𝟙_ (CochainComplex (PointMod ℓ k) ℤ))
  let r := (DerivedCategory.singleFunctor (PointMod ℓ k) 0).preimage
    (e.inv ≫ (pointScalar ℓ k c).asHom ≫ e.hom)
  have hr : (DerivedCategory.singleFunctor (PointMod ℓ k) 0).map r =
      e.inv ≫ (pointScalar ℓ k c).asHom ≫ e.hom := Functor.map_preimage _ _
  let hd : HasRightDual ((shiftFunctor (DerivedCategory (PointMod ℓ k)) m).obj
      ((DerivedCategory.singleFunctor (PointMod ℓ k) 0).obj (𝟙_ _))) :=
    hasRightDualOfIso ((shiftFunctor _ m).mapIso e.symm)
  rw [trace_eq_of_iso ((shiftFunctor _ m).mapIso e) _
    ((shiftFunctor _ m).map ((DerivedCategory.singleFunctor (PointMod ℓ k) 0).map r))
    (by simp only [Functor.mapIso_hom, ← Functor.map_comp, hr, Iso.hom_inv_id_assoc])]
  rw [DerivedCategory.trace_shiftFunctor_map_singleFunctor_map, hr]
  change e.hom ≫ ((m.negOnePow : ℤ) • (e.inv ≫ (pointScalar ℓ k c).asHom ≫ e.hom)) ≫ e.inv = _
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

-- the instances on the ambient derived category of modules are found through long searches
/-- **The trace is the supertrace on the graded pieces**: for an object `Y` of `D(Mod_{ℚ̲̄_ℓ,s})`
which is a finite direct sum of shifts `𝟙⟦nⱼ⟧` of the unit, the categorical trace of an
endomorphism `w` of `Y` is the alternating sum `∑ₙ (-1)ⁿ tr(w | Hⁿ(Y))` of the traces on the
graded pieces `Hⁿ(Y) = Hom(𝟙⟦n⟧, Y)` (blueprint `proposition-properties-trace`, item (4)). -/
theorem trace_eq_pointScalar_sum {Y : DerivedCategory (PointMod ℓ k)} [HasRightDual Y]
    (D : ShiftDecomposition (𝟙_ _) Y) (s : Finset ℤ) (hs : ∀ j, D.deg j ∈ s)
    [∀ n, FiniteDimensional (PadicAlgCl ℓ) ((gradedHom ℓ k n).obj Y)] (w : Y ⟶ Y) :
    trace w = (pointScalar ℓ k (∑ n ∈ s, (n.negOnePow : ℤ) •
      LinearMap.trace (PadicAlgCl ℓ) _ ((gradedHom ℓ k n).map w).hom)).asHom := by
  let c : D.ι → PadicAlgCl ℓ := fun j ↦
    (shiftedUnitEquiv ℓ k (D.deg j)).symm (gradedHomMk ℓ k (D.incl j ≫ w ≫ D.proj j))
  have hc (j : D.ι) : D.incl j ≫ w ≫ D.proj j =
      gradedHomHom ℓ k (shiftedUnitEquiv ℓ k (D.deg j) (c j)) := by
    simp only [c, LinearEquiv.apply_symm_apply]
    rfl
  rw [D.trace_eq_sum w]
  simp_rw [D.linearMapTrace_eq_sum (gradedHom ℓ k _) w, hc,
    trace_gradedHomHom_shiftedUnitEquiv, linearMapTrace_gradedHom_map_shiftedUnitEquiv,
    Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', hs, ite_true]
  rw [map_sum]
  simp only [map_zsmul, End.sum_asHom, End.zsmul_asHom]

end TraceFormula

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)]

section Additivity

/-- The shift `Hⁿ⁻¹(Y) ⟶ Hⁿ(Y⟦1⟧)`, `x ↦ x⟦1⟧` through `𝟙⟦n⟧ ≅ 𝟙⟦n - 1⟧⟦1⟧`. -/
noncomputable def gradedHomShift (n : ℤ) (Y : DerivedCategory (PointMod ℓ k)) :
    (gradedHom ℓ k (n - 1)).obj Y →ₗ[PadicAlgCl ℓ]
      (gradedHom ℓ k n).obj ((shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).obj Y) where
  toFun x := gradedHomMk ℓ k
    ((shiftFunctorAdd' (DerivedCategory (PointMod ℓ k)) (n - 1) 1 n (by lia)).hom.app (𝟙_ _) ≫
      (shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).map (gradedHomHom ℓ k x))
  map_add' x y := by
    change _ ≫ (shiftFunctor _ (1 : ℤ)).map (gradedHomHom ℓ k x + gradedHomHom ℓ k y) =
      _ ≫ (shiftFunctor _ (1 : ℤ)).map (gradedHomHom ℓ k x) +
        _ ≫ (shiftFunctor _ (1 : ℤ)).map (gradedHomHom ℓ k y)
    rw [Functor.map_add, Preadditive.comp_add]
  map_smul' c x := by
    change _ ≫ (shiftFunctor _ (1 : ℤ)).map
        ((shiftFunctor _ (n - 1)).map (pointScalar ℓ k c).asHom ≫ gradedHomHom ℓ k x) =
      (shiftFunctor _ n).map (pointScalar ℓ k c).asHom ≫ _ ≫
        (shiftFunctor _ (1 : ℤ)).map (gradedHomHom ℓ k x)
    have h :=
      (shiftFunctorAdd' (DerivedCategory (PointMod ℓ k)) (n - 1) 1 n (by lia)).hom.naturality
        (pointScalar ℓ k c).asHom
    simp only [Functor.comp_map] at h
    rw [Functor.map_comp, reassoc_of% h]

lemma gradedHomHom_gradedHomShift (n : ℤ) (Y : DerivedCategory (PointMod ℓ k))
    (x : (gradedHom ℓ k (n - 1)).obj Y) :
    gradedHomHom ℓ k (gradedHomShift ℓ k n Y x) =
      (shiftFunctorAdd' (DerivedCategory (PointMod ℓ k)) (n - 1) 1 n (by lia)).hom.app (𝟙_ _) ≫
        (shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).map (gradedHomHom ℓ k x) :=
  rfl

lemma bijective_gradedHomShift (n : ℤ) (Y : DerivedCategory (PointMod ℓ k)) :
    Function.Bijective (gradedHomShift ℓ k n Y) := by
  constructor
  · intro x y h
    have h' := congrArg (gradedHomHom ℓ k) h
    rw [gradedHomHom_gradedHomShift, gradedHomHom_gradedHomShift, cancel_epi] at h'
    exact (shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).map_injective h'
  · intro u
    refine ⟨gradedHomMk ℓ k ((shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).preimage
      ((shiftFunctorAdd' (DerivedCategory (PointMod ℓ k)) (n - 1) 1 n (by lia)).inv.app (𝟙_ _) ≫
        gradedHomHom ℓ k u)), ?_⟩
    change gradedHomHom ℓ k (gradedHomShift ℓ k n Y _) = gradedHomHom ℓ k u
    rw [gradedHomHom_gradedHomShift]
    change _ ≫ (shiftFunctor _ (1 : ℤ)).map ((shiftFunctor _ (1 : ℤ)).preimage _) = _
    rw [Functor.map_preimage, Iso.hom_inv_id_app_assoc]

/-- `gradedHomShift` is compatible with the maps induced by morphisms. -/
lemma gradedHomShift_map (n : ℤ) {Y Y' : DerivedCategory (PointMod ℓ k)} (h : Y ⟶ Y')
    (x : (gradedHom ℓ k (n - 1)).obj Y) :
    gradedHomShift ℓ k n Y' (((gradedHom ℓ k (n - 1)).map h).hom x) =
      ((gradedHom ℓ k n).map ((shiftFunctor _ (1 : ℤ)).map h)).hom (gradedHomShift ℓ k n Y x) := by
  change _ ≫ (shiftFunctor _ (1 : ℤ)).map (gradedHomHom ℓ k x ≫ h) =
    (_ ≫ (shiftFunctor _ (1 : ℤ)).map (gradedHomHom ℓ k x)) ≫ (shiftFunctor _ (1 : ℤ)).map h
  rw [Functor.map_comp, Category.assoc]

/-- The connecting map `Hⁿ(Y₃) ⟶ Hⁿ⁻¹(Y₁)` of a morphism `δ : Y₃ ⟶ Y₁⟦1⟧`. -/
noncomputable def gradedHomConnecting (n : ℤ) {Y₃ Y₁ : DerivedCategory (PointMod ℓ k)}
    (δ : Y₃ ⟶ (shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).obj Y₁) :
    (gradedHom ℓ k n).obj Y₃ →ₗ[PadicAlgCl ℓ] (gradedHom ℓ k (n - 1)).obj Y₁ :=
  (LinearEquiv.ofBijective _ (bijective_gradedHomShift ℓ k n Y₁)).symm.toLinearMap ∘ₗ
    ((gradedHom ℓ k n).map δ).hom

lemma gradedHomShift_gradedHomConnecting (n : ℤ) {Y₃ Y₁ : DerivedCategory (PointMod ℓ k)}
    (δ : Y₃ ⟶ (shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).obj Y₁)
    (y : (gradedHom ℓ k n).obj Y₃) :
    gradedHomShift ℓ k n Y₁ (gradedHomConnecting ℓ k n δ y) = ((gradedHom ℓ k n).map δ).hom y :=
  (LinearEquiv.ofBijective _ (bijective_gradedHomShift ℓ k n Y₁)).apply_symm_apply _

/-- The maps induced on `Hⁿ` by a commutative square `v ≫ f = f ≫ v'` commute. -/
lemma gradedHom_map_comp_comm (n : ℤ) {Y Y' : DerivedCategory (PointMod ℓ k)} {f : Y ⟶ Y'}
    {v : Y ⟶ Y} {v' : Y' ⟶ Y'} (h : v ≫ f = f ≫ v') :
    ((gradedHom ℓ k n).map v').hom ∘ₗ ((gradedHom ℓ k n).map f).hom =
      ((gradedHom ℓ k n).map f).hom ∘ₗ ((gradedHom ℓ k n).map v).hom := by
  rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp, h]

section Exact

variable {Y₁ Y₂ Y₃ : DerivedCategory (PointMod ℓ k)} {f : Y₁ ⟶ Y₂} {g : Y₂ ⟶ Y₃}
  {δ : Y₃ ⟶ (shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).obj Y₁}

/-- Exactness of `Hⁿ(Y₁) ⟶ Hⁿ(Y₂) ⟶ Hⁿ(Y₃)` for a distinguished triangle. -/
lemma exact_gradedHom_map_map (n : ℤ) (hT : Triangle.mk f g δ ∈ distTriang _) :
    Function.Exact ((gradedHom ℓ k n).map f).hom ((gradedHom ℓ k n).map g).hom := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ _ hT (gradedHomHom ℓ k y) hy
    exact ⟨gradedHomMk ℓ k x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    change (gradedHomHom ℓ k x ≫ f) ≫ g = 0
    rw [Category.assoc, show f ≫ g = 0 from comp_distTriang_mor_zero₁₂ _ hT, Limits.comp_zero]

/-- Exactness of `Hⁿ(Y₂) ⟶ Hⁿ(Y₃) ⟶ Hⁿ⁻¹(Y₁)` for a distinguished triangle. -/
lemma exact_gradedHom_map_gradedHomConnecting (n : ℤ) (hT : Triangle.mk f g δ ∈ distTriang _) :
    Function.Exact ((gradedHom ℓ k n).map g).hom (gradedHomConnecting ℓ k n δ) := by
  intro y
  constructor
  · intro hy
    have hy' : ((gradedHom ℓ k n).map δ).hom y = 0 := by
      rw [← gradedHomShift_gradedHomConnecting, hy, map_zero]
    obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₃ _ hT (gradedHomHom ℓ k y) hy'
    exact ⟨gradedHomMk ℓ k x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    apply (bijective_gradedHomShift ℓ k n Y₁).1
    rw [gradedHomShift_gradedHomConnecting, map_zero]
    change (gradedHomHom ℓ k x ≫ g) ≫ δ = 0
    rw [Category.assoc, show g ≫ δ = 0 from comp_distTriang_mor_zero₂₃ _ hT, Limits.comp_zero]

/-- Exactness of `Hⁿ(Y₃) ⟶ Hⁿ⁻¹(Y₁) ⟶ Hⁿ⁻¹(Y₂)` for a distinguished triangle. -/
lemma exact_gradedHomConnecting_gradedHom_map (n : ℤ) (hT : Triangle.mk f g δ ∈ distTriang _) :
    Function.Exact (gradedHomConnecting ℓ k n δ) ((gradedHom ℓ k (n - 1)).map f).hom := by
  intro x
  constructor
  · intro hx
    have hx0 : ((gradedHom ℓ k (n - 1)).map f).hom x = 0 := hx
    have hx' : gradedHomHom ℓ k (gradedHomShift ℓ k n Y₁ x) ≫
        (shiftFunctor _ (1 : ℤ)).map f = 0 := by
      rw [gradedHomHom_gradedHomShift, Category.assoc, ← Functor.map_comp,
        ← gradedHomHom_map_apply, hx0]
      change _ ≫ (shiftFunctor _ (1 : ℤ)).map 0 = 0
      rw [Functor.map_zero, Limits.comp_zero]
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₁ _ hT _ hx'
    refine ⟨gradedHomMk ℓ k y, ?_⟩
    show gradedHomConnecting ℓ k n δ (gradedHomMk ℓ k y) = x
    apply (bijective_gradedHomShift ℓ k n Y₁).1
    rw [gradedHomShift_gradedHomConnecting]
    exact hy.symm
  · rintro ⟨y, rfl⟩
    refine ((gradedHomShift ℓ k n Y₂).map_eq_zero_iff (bijective_gradedHomShift ℓ k n Y₂).1).1 ?_
    change gradedHomShift ℓ k n Y₂ (((gradedHom ℓ k (n - 1)).map f).hom
        (gradedHomConnecting ℓ k n δ y)) = 0
    rw [gradedHomShift_map, gradedHomShift_gradedHomConnecting]
    change (gradedHomHom ℓ k y ≫ δ) ≫ (shiftFunctor _ (1 : ℤ)).map f = 0
    rw [Category.assoc]
    erw [comp_distTriang_mor_zero₃₁ _ hT]
    rw [Limits.comp_zero]

/-- The connecting maps commute with the maps induced by an endomorphism of the triangle. -/
lemma gradedHomConnecting_comm (n : ℤ) {v₁ : Y₁ ⟶ Y₁} {v₃ : Y₃ ⟶ Y₃}
    (h₃ : v₃ ≫ δ = δ ≫ (shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).map v₁) :
    ((gradedHom ℓ k (n - 1)).map v₁).hom ∘ₗ gradedHomConnecting ℓ k n δ =
      gradedHomConnecting ℓ k n δ ∘ₗ ((gradedHom ℓ k n).map v₃).hom := by
  refine LinearMap.ext fun y ↦ (bijective_gradedHomShift ℓ k n Y₁).1 ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, gradedHomShift_map,
    gradedHomShift_gradedHomConnecting, gradedHomShift_gradedHomConnecting]
  change (gradedHomHom ℓ k y ≫ δ) ≫ (shiftFunctor _ (1 : ℤ)).map v₁ =
    (gradedHomHom ℓ k y ≫ v₃) ≫ δ
  rw [Category.assoc, Category.assoc, h₃]

end Exact

attribute [local instance] DerivedCategory.braidedCategory'

/-- **Additivity of the trace along distinguished triangles over the point**, in the ambient
derived category: for a distinguished triangle `Y₁ ⟶ Y₂ ⟶ Y₃ ⟶ Y₁⟦1⟧` of finite direct sums of
shifts of the unit and an endomorphism `(v₁, v₂, v₃)` of it, `tr v₂ = tr v₁ + tr v₃`. -/
theorem trace_eq_trace_add_trace_of_distTriang_of_shiftDecomposition [IsSepClosed k]
    [Fact (ringChar k).Prime]
    {Y₁ Y₂ Y₃ : DerivedCategory (PointMod ℓ k)} [HasRightDual Y₁] [HasRightDual Y₂]
    [HasRightDual Y₃] (D₁ : ShiftDecomposition (𝟙_ _) Y₁) (D₂ : ShiftDecomposition (𝟙_ _) Y₂)
    (D₃ : ShiftDecomposition (𝟙_ _) Y₃) (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃)
    (δ : Y₃ ⟶ (shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).obj Y₁)
    (hT : Triangle.mk f g δ ∈ distTriang _) (v₁ : Y₁ ⟶ Y₁) (v₂ : Y₂ ⟶ Y₂) (v₃ : Y₃ ⟶ Y₃)
    (h₁ : v₁ ≫ f = f ≫ v₂) (h₂ : v₂ ≫ g = g ≫ v₃)
    (h₃ : v₃ ≫ δ = δ ≫ (shiftFunctor (DerivedCategory (PointMod ℓ k)) (1 : ℤ)).map v₁) :
    trace v₂ = trace v₁ + trace v₃ := by
  have : ∀ n, FiniteDimensional (PadicAlgCl ℓ) ((gradedHom ℓ k n).obj Y₁) :=
    fun n ↦ D₁.finiteDimensional_obj (gradedHom ℓ k n)
  have : ∀ n, FiniteDimensional (PadicAlgCl ℓ) ((gradedHom ℓ k n).obj Y₂) :=
    fun n ↦ D₂.finiteDimensional_obj (gradedHom ℓ k n)
  have : ∀ n, FiniteDimensional (PadicAlgCl ℓ) ((gradedHom ℓ k n).obj Y₃) :=
    fun n ↦ D₃.finiteDimensional_obj (gradedHom ℓ k n)
  let s := Finset.univ.image D₁.deg ∪ Finset.univ.image D₂.deg ∪ Finset.univ.image D₃.deg
  have hs₁ (j : D₁.ι) : D₁.deg j ∈ s := by simp [s]
  have hs₂ (j : D₂.ι) : D₂.deg j ∈ s := by simp [s]
  have hs₃ (j : D₃.ι) : D₃.deg j ∈ s := by simp [s]
  have hsub {Y : DerivedCategory (PointMod ℓ k)} (D : ShiftDecomposition (𝟙_ _) Y)
      (hD : ∀ j, D.deg j ∈ s) (n : ℤ) (hn : n ∉ s) :
      Subsingleton ((gradedHom ℓ k n).obj Y) :=
    D.subsingleton_obj (gradedHom ℓ k n) fun j ↦
      have := subsingleton_hom_shiftedUnit ℓ k n (D.deg j) (fun h ↦ hn (h ▸ hD j))
      inferInstanceAs (Subsingleton (shiftedUnit ℓ k n ⟶ shiftedUnit ℓ k (D.deg j)))
  have key := LinearMap.sum_negOnePow_smul_trace_sub_trace_sub_trace_eq_zero
    (fun n ↦ (gradedHom ℓ k n).obj Y₁) (fun n ↦ (gradedHom ℓ k n).obj Y₂)
    (fun n ↦ (gradedHom ℓ k n).obj Y₃) (fun n ↦ ((gradedHom ℓ k n).map f).hom)
    (fun n ↦ ((gradedHom ℓ k n).map g).hom) (fun n ↦ gradedHomConnecting ℓ k n δ)
    (fun n ↦ exact_gradedHom_map_map ℓ k n hT)
    (fun n ↦ exact_gradedHom_map_gradedHomConnecting ℓ k n hT)
    (fun n ↦ exact_gradedHomConnecting_gradedHom_map ℓ k n hT)
    (fun n ↦ ((gradedHom ℓ k n).map v₁).hom) (fun n ↦ ((gradedHom ℓ k n).map v₂).hom)
    (fun n ↦ ((gradedHom ℓ k n).map v₃).hom) (fun n ↦ gradedHom_map_comp_comm ℓ k n h₁)
    (fun n ↦ gradedHom_map_comp_comm ℓ k n h₂) (fun n ↦ gradedHomConnecting_comm ℓ k n h₃) s
    (hsub D₁ hs₁) (hsub D₃ hs₃)
  rw [trace_eq_pointScalar_sum ℓ k D₁ s hs₁, trace_eq_pointScalar_sum ℓ k D₂ s hs₂,
    trace_eq_pointScalar_sum ℓ k D₃ s hs₃, ← End.add_asHom,
    ← (pointScalar ℓ k).map_add, ← Finset.sum_add_distrib]
  congr 2
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← key]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [smul_sub]
  abel

end Additivity

end AlgebraicGeometry.ProEtale.CondensedRing
