/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.MiddleExtension
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.WeilSheaf.UpperStarPointwise
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact

/-!
# Purity of real lisse Weil sheaves on curves

Let `C₀` be a smooth geometrically connected curve over a finite field `k₀` and `𝒢₀` an `ι`-real
lisse Weil sheaf on `C₀`. Every irreducible constituent of `𝒢₀` is punctually `ι`-pure, of its
determinant weight. This is the main theorem of the blueprint section `chap-Purity-of-real-sheaves`,
formalised there on the side of representations of the Weil group
(`AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal`); this file states
it for Weil sheaves, with irreducible constituents rendered as irreducible lisse subquotients
`𝒢₂ / 𝒢₁` of lisse Weil subsheaves `𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢₀`.

## Proof

The statement is transported along the lisse sheaf–representation equivalence
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse` for a Weil group `W(C₀)`. Kernels and
cokernels of morphisms of lisse Weil sheaves are lisse, and subrepresentations and quotients of
lisse Weil representations are lisse, so monomorphisms, epimorphisms and cokernels in the two
full subcategories are the usual ones. Hence the representation of `𝒢₂ / 𝒢₁` is the subquotient
of the representation `ρ` of `𝒢₀` cut out by the images of `𝒢₁` and `𝒢₂`, and it is irreducible,
being a simple object. It is thus a constituent of the `ι`-real lisse representation `ρ`, pure of
its determinant weight; the stalks with their local Frobenius are the representation spaces with
the Frobenius elements, so the eigenvalues and determinants agree.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`:
  blueprint `theorem-purity-real-sheaves-curves--1` (`theorem-purity-real-sheaves-curves--1`).
- `AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel`: the weaker form
  asserting only the existence of a weight.
- `AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_directImage`: blueprint
  `proposition-weights-j-boundary-points--1` (`proposition-weights-j-boundary-points`).
- `AlgebraicGeometry.WeilSheaf.IsLisse.isPunctuallyPureOfWeight_of_upperStar`: blueprint
  `corollary-unramified-boundary-point--2`, consequence clause
  (`proposition-weights-j-boundary-points`), deduced from boundary semicontinuity applied to the
  sheaf and to its dual.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace FrobeniusModule

variable {K : Type*} [Field K]

/-- If a Frobenius module `M` is identified with a finite-dimensional space `V` with an
endomorphism `T`, compatibly with the Frobenius, then the Frobenius of `M` and `T` have the same
characteristic polynomial. -/
theorem charpoly_frobeniusEnd_eq_of_linearEquiv (M : FrobeniusModule K) {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {T : Module.End K V}
    (f : M.carrier ≃ₗ[K] V) (hf : ∀ v, f (M.frobenius v) = T (f v)) :
    M.frobeniusEnd.charpoly = T.charpoly := by
  have : FiniteDimensional K M.carrier := Module.Finite.equiv f.symm
  refine LinearMap.charpoly_eq_of_comp_eq f (LinearMap.ext fun v ↦ ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, frobeniusEnd_apply,
    LinearEquiv.coe_toLinearMap, hf]

private theorem localPolynomial_eq_of_linearEquiv (M : FrobeniusModule K) {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {T : Module.End K V}
    (f : M.carrier ≃ₗ[K] V) (hf : ∀ v, f (M.frobenius v) = T (f v)) :
    M.localPolynomial = T.charpolyRev :=
  congrArg Polynomial.reverse (charpoly_frobeniusEnd_eq_of_linearEquiv M f hf)

/-- If a Frobenius module `M` is identified with a space `V` with an endomorphism `T`,
compatibly with the Frobenius, then the Frobenius of `M` and `T` have the same determinant. -/
theorem det_frobeniusEnd_eq_of_linearEquiv (M : FrobeniusModule K) {V : Type*}
    [AddCommGroup V] [Module K V] {T : Module.End K V}
    (f : M.carrier ≃ₗ[K] V) (hf : ∀ v, f (M.frobenius v) = T (f v)) :
    LinearMap.det M.frobeniusEnd = LinearMap.det T := by
  have hT : (f : M.carrier →ₗ[K] V) ∘ₗ M.frobeniusEnd ∘ₗ (f.symm : V →ₗ[K] M.carrier) = T :=
    LinearMap.ext fun v ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.coe_toLinearMap, frobeniusEnd_apply, hf, LinearEquiv.apply_symm_apply]
  rw [← hT, LinearMap.det_conj]

end FrobeniusModule

namespace AlgebraicGeometry.WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} {l : ℕ} [Fact l.Prime]

/-- A monomorphism of lisse Weil representations is injective: its kernel is a lisse Weil
representation. -/
theorem isLisseRep.injective_of_mono {X Y : (W.isLisseRep l).FullSubcategory} (f : X ⟶ Y)
    [Mono f] : Function.Injective f.hom.hom := by
  let S := f.hom.hom.ker
  have hS : ∀ g, S.toSubmodule ≤ S.toSubmodule.comap (X.obj.ρ g) :=
    fun g _ hv ↦ S.apply_mem_toSubmodule g hv
  have : Mono (Rep.subtype X.obj S.toSubmodule hS) :=
    (Rep.mono_iff_injective _).2 Subtype.val_injective
  let Z : (W.isLisseRep l).FullSubcategory :=
    ⟨_, (W.isLisseRep l).prop_of_mono (Rep.subtype X.obj S.toSubmodule hS) X.property⟩
  let ι : Z ⟶ X := ObjectProperty.homMk (Rep.subtype X.obj S.toSubmodule hS)
  have h0 : ι = 0 := (cancel_mono f).1 <| ObjectProperty.hom_ext _ <| Rep.hom_ext <|
    Representation.IntertwiningMap.ext <| LinearMap.ext fun v ↦ by
      rw [zero_comp]
      exact v.2
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  exact congrArg (fun φ : Z ⟶ X ↦ φ.hom.hom ⟨v, hv⟩) h0

/-- An epimorphism of lisse Weil representations is surjective: its cokernel is a lisse Weil
representation. -/
theorem isLisseRep.surjective_of_epi {X Y : (W.isLisseRep l).FullSubcategory} (f : X ⟶ Y)
    [Epi f] : Function.Surjective f.hom.hom := by
  let S := f.hom.hom.range
  have hS : ∀ g, S.toSubmodule ≤ S.toSubmodule.comap (Y.obj.ρ g) :=
    fun g _ hv ↦ S.apply_mem_toSubmodule g hv
  have : Epi (Rep.mkQ Y.obj S.toSubmodule hS) :=
    (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  let Z : (W.isLisseRep l).FullSubcategory :=
    ⟨_, (W.isLisseRep l).prop_of_epi (Rep.mkQ Y.obj S.toSubmodule hS) Y.property⟩
  let π : Y ⟶ Z := ObjectProperty.homMk (Rep.mkQ Y.obj S.toSubmodule hS)
  have h0 : π = 0 := (cancel_epi f).1 <| ObjectProperty.hom_ext _ <| Rep.hom_ext <|
    Representation.IntertwiningMap.ext <| LinearMap.ext fun v ↦
      (Submodule.Quotient.mk_eq_zero _).2 ⟨v, rfl⟩
  intro y
  have hy := congrArg (fun φ : Y ⟶ Z ↦ φ.hom.hom y) h0
  exact (Submodule.Quotient.mk_eq_zero _).1 hy

/-- If `c : B ⟶ Q` is a cokernel of `f : A ⟶ B` in the category of lisse Weil representations,
then the kernel of `c` is the image of `f`: the quotient of `B` by the image of `f` is a lisse
Weil representation, through which `c` factors. -/
theorem isLisseRep.mem_range_of_isColimit {A B : (W.isLisseRep l).FullSubcategory}
    {f : A ⟶ B} {c : CokernelCofork f} (hc : IsColimit c) {v : B.obj.V}
    (hv : c.π.hom.hom v = 0) : v ∈ f.hom.hom.range := by
  let S := f.hom.hom.range
  have hS : ∀ g, S.toSubmodule ≤ S.toSubmodule.comap (B.obj.ρ g) :=
    fun g _ hv ↦ S.apply_mem_toSubmodule g hv
  have : Epi (Rep.mkQ B.obj S.toSubmodule hS) :=
    (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  let Z : (W.isLisseRep l).FullSubcategory :=
    ⟨_, (W.isLisseRep l).prop_of_epi (Rep.mkQ B.obj S.toSubmodule hS) B.property⟩
  let q : B ⟶ Z := ObjectProperty.homMk (Rep.mkQ B.obj S.toSubmodule hS)
  have hq : f ≫ q = 0 := ObjectProperty.hom_ext _ <| Rep.hom_ext <|
    Representation.IntertwiningMap.ext <| LinearMap.ext fun a ↦
      (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩
  obtain ⟨u, hu⟩ := CokernelCofork.IsColimit.desc' hc q hq
  have h := congrArg (fun φ : B ⟶ Z ↦ φ.hom.hom v) hu
  simp only [ObjectProperty.FullSubcategory.comp_hom, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply, hv, map_zero] at h
  exact (Submodule.Quotient.mk_eq_zero _).1 h.symm

/-- A simple object of the category of lisse Weil representations is an irreducible
representation: a subrepresentation of a lisse Weil representation is lisse. -/
theorem isLisseRep.isIrreducible_of_simple (X : (W.isLisseRep l).FullSubcategory) [Simple X] :
    X.obj.ρ.IsIrreducible := by
  refine Representation.isIrreducible_iff.2 ⟨?_, fun U hU ↦ ?_⟩
  · by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    refine Simple.not_isZero X ((IsZero.iff_id_eq_zero X).2 ?_)
    exact ObjectProperty.hom_ext _ <| Rep.hom_ext <| Representation.IntertwiningMap.ext <|
      LinearMap.ext fun v ↦ Subsingleton.elim _ _
  · have hS : ∀ g, U ≤ U.comap (X.obj.ρ g) := fun g v hv ↦ hU g v hv
    have hmono : Mono (Rep.subtype X.obj U hS) :=
      (Rep.mono_iff_injective _).2 Subtype.val_injective
    let Z : (W.isLisseRep l).FullSubcategory :=
      ⟨_, (W.isLisseRep l).prop_of_mono (Rep.subtype X.obj U hS) X.property⟩
    let ι : Z ⟶ X := ObjectProperty.homMk (Rep.subtype X.obj U hS)
    have : Mono ι := (ObjectProperty.ι _).mono_of_mono_map hmono
    by_cases h0 : ι = 0
    · refine Or.inl ((Submodule.eq_bot_iff _).2 fun v hv ↦ ?_)
      exact congrArg (fun φ : Z ⟶ X ↦ φ.hom.hom ⟨v, hv⟩) h0
    · have : IsIso ι := isIso_of_mono_of_nonzero h0
      have : IsIso (Rep.subtype X.obj U hS) := (ObjectProperty.ι _).map_isIso ι
      refine Or.inr (Submodule.eq_top_iff'.2 fun v ↦ ?_)
      obtain ⟨u, hu⟩ := (Rep.epi_iff_surjective (Rep.subtype X.obj U hS)).1 inferInstance v
      exact hu ▸ u.2

end AlgebraicGeometry.WeilGroup

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Lisse

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- A monomorphism in the category of lisse Weil sheaves is a monomorphism of Weil sheaves: its
kernel is lisse. -/
theorem IsLisse.mono_hom_of_mono
    {F G : ObjectProperty.FullSubcategory (fun F : WeilSheaf k₀ l X ↦ F.IsLisse)} (f : F ⟶ G)
    [Mono f] : Mono f.hom := by
  let Z : ObjectProperty.FullSubcategory (fun F : WeilSheaf k₀ l X ↦ F.IsLisse) :=
    ⟨kernel f.hom, (IsLisse.kernel_cokernel F.property G.property f.hom).1⟩
  have h0 : (ObjectProperty.homMk (kernel.ι f.hom) : Z ⟶ F) = 0 :=
    (cancel_mono f).1 (ObjectProperty.hom_ext _ (by simp))
  exact Preadditive.mono_of_kernel_zero (congrArg InducedCategory.Hom.hom h0)

/-- An irreducible lisse Weil sheaf is a simple object of the category of lisse Weil sheaves. -/
theorem IsIrreducibleLisse.simple {F : WeilSheaf k₀ l X} (hF : F.IsIrreducibleLisse) :
    Simple (⟨F, hF.1⟩ :
      ObjectProperty.FullSubcategory (fun F : WeilSheaf k₀ l X ↦ F.IsLisse)) where
  mono_isIso_iff_nonzero {Y} f _ := by
    have := IsLisse.mono_hom_of_mono f
    refine ⟨fun _ h0 ↦ hF.2.1 ((IsZero.iff_id_eq_zero F).2 ?_), fun h0 ↦ ?_⟩
    · subst h0
      have h := congrArg InducedCategory.Hom.hom (IsIso.inv_hom_id (0 : Y ⟶ ⟨F, hF.1⟩))
      rw [comp_zero] at h
      exact h.symm
    · rcases hF.2.2 Y.obj f.hom this Y.property with hz | hiso
      · exact absurd (ObjectProperty.hom_ext _ (hz.eq_of_src _ _)) h0
      · have : IsIso ((ObjectProperty.ι _).map f) := hiso
        exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map f

end Lisse

variable {ι : PadicAlgCl l →+* ℂ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]

/-- **Purity of real lisse sheaves on curves** (blueprint: `theorem-purity-real-sheaves-curves--1`,
`theorem-purity-real-sheaves-curves--1`, of the section `chap-Purity-of-real-sheaves`). Let `C₀` be
a smooth geometrically connected curve over `k₀` and `𝒢₀` an `ι`-real lisse Weil sheaf on `C₀`.
Every irreducible constituent `V` of `𝒢₀`, that is, every irreducible lisse quotient `V = 𝒢₂ / 𝒢₁`
of lisse Weil subsheaves `𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢₀`, is punctually `ι`-pure of its determinant weight `w`: at
every closed point `x`, `rank(V_x̄) * w` is the `ι`-weight of `det(F_x | V_x̄)`.

The statement is transported from the representation side
(`AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal`) along the lisse
sheaf–representation equivalence (`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`). -/
theorem IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight
    {𝒢 : WeilSheaf k₀ l C} (h𝒢 : 𝒢.IsLisse) (hreal : 𝒢.IsReal ι) {𝒢₁ 𝒢₂ : WeilSheaf k₀ l C}
    (i : 𝒢₁ ⟶ 𝒢₂) (j : 𝒢₂ ⟶ 𝒢) [Mono i] [Mono j] (h₁ : 𝒢₁.IsLisse) (h₂ : 𝒢₂.IsLisse)
    (hirr : (cokernel i).IsIrreducibleLisse) :
    ∃ w : ℝ, (cokernel i).IsPunctuallyPureOfWeight ι w ∧ ∀ x : C.finitePoints,
      Module.finrank (PadicAlgCl l) ((cokernel i).stalk x).carrier * w =
        WeilGroup.frobeniusWeight ι ((C ↘ Spec (CommRingCat.of k₀)).residueCard x.1)
          (LinearMap.det ((cokernel i).stalk x).frobeniusEnd) := by
  have : IsCurve (C ↘ Spec (CommRingCat.of k₀)) :=
    { krullDim_le_one := by
        exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension
          (C ↘ Spec (CommRingCat.of k₀)) 1 }
  obtain ⟨W⟩ := WeilGroup.nonempty (C ↘ Spec (CommRingCat.of k₀))
  obtain ⟨e, hst, -, -, -⟩ := W.exists_equivalence_isLisse l
  -- the subquotient `𝒢₂ / 𝒢₁` in the category of lisse Weil sheaves
  let G : ObjectProperty.FullSubcategory (fun F : WeilSheaf k₀ l C ↦ F.IsLisse) := ⟨𝒢, h𝒢⟩
  have hrealG : G.obj.IsReal ι := hreal
  let G₁ : ObjectProperty.FullSubcategory (fun F : WeilSheaf k₀ l C ↦ F.IsLisse) := ⟨𝒢₁, h₁⟩
  let G₂ : ObjectProperty.FullSubcategory (fun F : WeilSheaf k₀ l C ↦ F.IsLisse) := ⟨𝒢₂, h₂⟩
  let Q : ObjectProperty.FullSubcategory (fun F : WeilSheaf k₀ l C ↦ F.IsLisse) :=
    ⟨cokernel i, hirr.1⟩
  let i' : G₁ ⟶ G₂ := ObjectProperty.homMk i
  let j' : G₂ ⟶ G := ObjectProperty.homMk j
  let π' : G₂ ⟶ Q := ObjectProperty.homMk (cokernel.π i)
  have : Mono i' := (ObjectProperty.ι _).mono_of_mono_map (inferInstanceAs (Mono i))
  have : Mono j' := (ObjectProperty.ι _).mono_of_mono_map (inferInstanceAs (Mono j))
  have : Epi π' := (ObjectProperty.ι _).epi_of_epi_map (inferInstanceAs (Epi (cokernel.π i)))
  have hπ : i' ≫ π' = 0 := ObjectProperty.hom_ext _ (cokernel.condition i)
  have hc : IsColimit (CokernelCofork.ofπ π' hπ) :=
    CokernelCofork.IsColimit.ofπ' π' hπ fun k hk ↦
      ⟨ObjectProperty.homMk (cokernel.desc i k.hom (congrArg InducedCategory.Hom.hom hk)),
        ObjectProperty.hom_ext _ (cokernel.π_desc _ _ _)⟩
  have hc' := (CokernelCofork.ofπ π' hπ).mapIsColimit hc e.functor
  -- the corresponding lisse Weil representations
  set P := e.functor.obj G
  set A₂ := e.functor.obj G₂
  set R := e.functor.obj Q
  have := P.property.1
  have := R.property.1
  let fi := (e.functor.map i').hom.hom
  let fj := (e.functor.map j').hom.hom
  let fπ := (e.functor.map π').hom.hom
  have hfj : Function.Injective fj := WeilGroup.isLisseRep.injective_of_mono _
  have hfπ : Function.Surjective fπ := WeilGroup.isLisseRep.surjective_of_epi _
  have hfiπ (v) : fπ (fi v) = 0 := by
    have h : e.functor.map i' ≫ e.functor.map π' = 0 := by
      rw [← e.functor.map_comp, hπ, e.functor.map_zero]
    simpa using congrArg (fun φ : _ ⟶ R ↦ φ.hom.hom v) h
  have hker {v} (hv : fπ v = 0) : v ∈ fi.range :=
    WeilGroup.isLisseRep.mem_range_of_isColimit hc' hv
  have hbot {x : R.obj.V} : x ∈ (⊥ : Subrepresentation R.obj.ρ) ↔ x = 0 := by
    change x ∈ (⊥ : Subrepresentation R.obj.ρ).toSubmodule ↔ _
    rw [Subrepresentation.toSubmodule_bot, Submodule.mem_bot]
  -- the representation of `𝒢₂ / 𝒢₁` is a subquotient of that of `𝒢`
  let M : Subrepresentation P.obj.ρ := fj.range
  let N : Subrepresentation P.obj.ρ := Subrepresentation.map fj fi.range
  have hNM : N ≤ M := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  let E₁ : ((⊤ : Subrepresentation A₂.obj.ρ).subquotient fi.range).Equiv
      ((⊤ : Subrepresentation R.obj.ρ).subquotient ⊥) :=
    Subrepresentation.subquotientEquivOfIntertwiningMap fπ (fun _ _ ↦ trivial)
      (fun _ _ ⟨y, hy⟩ ↦ hbot.2 (hy ▸ hfiπ y)) (fun _ _ hx ↦ hker (hbot.1 hx))
      fun y _ ↦ by
        obtain ⟨x, rfl⟩ := hfπ y
        exact ⟨x, trivial, hbot.2 (sub_self _)⟩
  let E₂ : ((⊤ : Subrepresentation A₂.obj.ρ).subquotient fi.range).Equiv (M.subquotient N) :=
    Subrepresentation.subquotientEquivOfIntertwiningMap fj (fun x _ ↦ ⟨x, rfl⟩)
      (fun x _ hx ↦ ⟨x, hx, rfl⟩)
      (fun x _ hx ↦ by
        obtain ⟨y, hy, hyx⟩ := hx
        exact hfj hyx ▸ hy)
      fun y hy ↦ by
        obtain ⟨x, rfl⟩ := hy
        exact ⟨x, trivial, by
          simp only [Representation.IntertwiningMap.coe_toLinearMap, sub_self]
          exact N.toSubmodule.zero_mem⟩
  let E : R.obj.ρ.Equiv (M.subquotient N) :=
    (Subrepresentation.topSubquotientBotEquiv R.obj.ρ).symm.trans (E₁.symm.trans E₂)
  have : Simple Q := hirr.simple
  have : Simple R := simple_obj e.functor Q
  have hσ : R.obj.ρ.IsConstituent P.obj.ρ :=
    ⟨WeilGroup.isLisseRep.isIrreducible_of_simple R, N, M, hNM,
      ⟨E.asModuleLinearEquiv.trans (M.subquotientAsModuleLinearEquiv N)⟩⟩
  -- the representation of `𝒢` is `ι`-real
  have hreal' : W.IsReal l P.obj.ρ ι := fun x n ↦ by
    obtain ⟨f, hf⟩ := hst G x
    have hpoly : (G.obj.stalk x).localPolynomial = W.localPolynomial l P.obj.ρ x :=
      FrobeniusModule.localPolynomial_eq_of_linearEquiv _ f hf
    have hcoeff := congrArg (fun p : Polynomial (PadicAlgCl l) ↦ ι (p.coeff n)) hpoly
    exact (congrArg (starRingEnd ℂ) hcoeff).symm.trans ((hrealG x n).trans hcoeff)
  -- purity of the constituent, transported back to the stalks
  obtain ⟨γ, hγ⟩ : ∃ γ, W.HasDetWeight l R.obj.ρ ι γ := ⟨_, R.property.2.hasDetWeight ι⟩
  have hpure := WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal W l P.obj.ρ ι
    P.property.2 hreal' R.obj.ρ hσ hγ
  have hqx (x : C.finitePoints) :
      (C ↘ Spec (CommRingCat.of k₀)).residueCard x.1 = C.pointNorm x.1 :=
    (Scheme.Hom.pointNorm_eq_pow_degreeOver _ x.2).symm
  refine ⟨γ, fun x α hα ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨f, hf⟩ := hst Q x
    have : FiniteDimensional (PadicAlgCl l) (Q.obj.stalk x).carrier := Module.Finite.equiv f.symm
    have hα' : α ∈ W.localEigenvalues l R.obj.ρ x := by
      rw [WeilGroup.localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
        ← FrobeniusModule.charpoly_frobeniusEnd_eq_of_linearEquiv _ f hf,
        ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
      exact hα
    have : Finite (C.residueField x.1) := C.mem_finitePoints.mp x.2
    have hq : 1 < C.pointNorm x.1 := Finite.one_lt_card
    rw [hqx]
    exact (WeilGroup.isOfWeight_iff_frobeniusWeight_eq hq
      (FrobeniusModule.ne_zero_of_hasEigenvalue hα)).2 (hpure x α hα')
  · obtain ⟨f, hf⟩ := hst Q x
    rw [show (cokernel i).stalk x = Q.obj.stalk x from rfl,
      FrobeniusModule.det_frobeniusEnd_eq_of_linearEquiv _ f hf, f.finrank_eq, hqx, hγ x]

/-- **Purity of real lisse sheaves on curves**, weak form (blueprint:
`theorem-purity-real-sheaves-curves--1`). Let `C₀` be a smooth geometrically
connected curve over `k₀` and `𝒢₀` an `ι`-real lisse Weil sheaf on `C₀`. Every irreducible
constituent of `𝒢₀`, that is, every irreducible lisse quotient `𝒢₂ / 𝒢₁` of lisse Weil subsheaves
`𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢₀`, is punctually `ι`-pure. The weight is the determinant weight by
`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`. -/
theorem IsReal.exists_isPunctuallyPureOfWeight_cokernel {𝒢 : WeilSheaf k₀ l C} (h𝒢 : 𝒢.IsLisse)
    (hreal : 𝒢.IsReal ι) {𝒢₁ 𝒢₂ : WeilSheaf k₀ l C} (i : 𝒢₁ ⟶ 𝒢₂) (j : 𝒢₂ ⟶ 𝒢) [Mono i]
    [Mono j] (h₁ : 𝒢₁.IsLisse) (h₂ : 𝒢₂.IsLisse) (hirr : (cokernel i).IsIrreducibleLisse) :
    ∃ w : ℝ, (cokernel i).IsPunctuallyPureOfWeight ι w :=
  (hreal.exists_isPunctuallyPureOfWeight_cokernel_detWeight h𝒢 i j h₁ h₂ hirr).imp
    fun _ h ↦ h.1


/-- *Boundary semicontinuity of weights* on a curve: let `j : U₀ ⟶ C₀` be a dense open immersion
into a smooth geometrically connected curve over `k₀`. If the lisse sheaf `F` on `U₀` has punctual
weights at most `β`, then so has its direct image `j_*F` at every closed point of `C₀`, including
the finitely many points outside `U₀`, where it may be singular.
(blueprint: `proposition-weights-j-boundary-points--1`) -/
theorem IsLisse.hasWeightsAtMost_directImage {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l U} (hF : F.IsLisse)
    {ι : PadicAlgCl l →+* ℂ} {β : ℝ} (hβ : F.HasWeightsAtMost ι β) :
    ((directImage j).obj F).HasWeightsAtMost ι β := by
  -- Step 0: an affine open neighbourhood `V` of `s`, a smooth geometrically connected affine
  -- curve, on which `j_* ℱ` is the direct image of `ℱ|_{j⁻¹ V}`; the affine case applies there.
  have : IsDominant j := ⟨hj⟩
  intro s α hα
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top s.1)
  have : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k₀))
  have : IsAffine V := hV
  have : Nonempty V := ⟨⟨s.1, hsV⟩⟩
  let : (V : Scheme.{u}).Over (Spec (CommRingCat.of k₀)) := ⟨V.ι ≫ C ↘ Spec (CommRingCat.of k₀)⟩
  have : V.ι.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  let : (j ⁻¹ᵁ V : Scheme.{u}).Over (Spec (CommRingCat.of k₀)) :=
    ⟨(j ⁻¹ᵁ V).ι ≫ U ↘ Spec (CommRingCat.of k₀)⟩
  have : (j ⁻¹ᵁ V).ι.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hpb : IsPullback (j ∣_ V) (j ⁻¹ᵁ V).ι V.ι j := isPullback_morphismRestrict j V
  have : (j ∣_ V).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change (j ∣_ V) ≫ V.ι ≫ C ↘ Spec (CommRingCat.of k₀) =
      (j ⁻¹ᵁ V).ι ≫ U ↘ Spec (CommRingCat.of k₀)
    rw [← Category.assoc, hpb.w, Category.assoc, comp_over j]⟩
  have : QuasiCompact (j ∣_ V) := MorphismProperty.of_isPullback hpb.flip ‹_›
  have : QuasiCompact (j ⁻¹ᵁ V).ι := MorphismProperty.of_isPullback hpb inferInstance
  have : IsDominant (j ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsDominant j› V
  -- `V` is a smooth geometrically connected affine curve
  have : SmoothOfRelativeDimension 1 ((V : Scheme.{u}) ↘ Spec (CommRingCat.of k₀)) :=
    (zero_add 1) ▸ (inferInstance :
      SmoothOfRelativeDimension (0 + 1) (V.ι ≫ C ↘ Spec (CommRingCat.of k₀)))
  have : GeometricallyConnected ((V : Scheme.{u}) ↘ Spec (CommRingCat.of k₀)) := by
    have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    have := GeometricallyIrreducible.of_smooth_of_geometricallyConnected
      (C ↘ Spec (CommRingCat.of k₀))
    have := GeometricallyIrreducible.comp_of_isOpenImmersion V.ι (C ↘ Spec (CommRingCat.of k₀))
    exact inferInstanceAs (GeometricallyConnected (V.ι ≫ C ↘ Spec (CommRingCat.of k₀)))
  -- the point `s` of `V`
  have hy : (⟨s.1, hsV⟩ : V) ∈ (V : Scheme.{u}).finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso V.ι _).1 s.2
  exact norm_le_of_hasEigenvalue_stalk_directImage_of_isPullback j ι hpb hF hβ ⟨_, hy⟩ s rfl hα


/-- *Upper weight bounds extend over the missing points.* Let `G` be a lisse Weil sheaf on a
smooth geometrically connected curve `C` over `k₀` and `j : U ↪ C` a dense open immersion. If
`j^*G` has weights at most `w`, then so has `G ≅ j_* j^* G`, by boundary semicontinuity
(`AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_directImage`). -/
theorem IsLisse.hasWeightsAtMost_of_upperStar {ι : PadicAlgCl l →+* ℂ}
    {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
    [QuasiCompact j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {G : WeilSheaf k₀ l C} (hG : G.IsLisse) {w : ℝ}
    (hw : ((WeilSheaf.upperStar j).obj G).HasWeightsAtMost ι w) : G.HasWeightsAtMost ι w := by
  obtain ⟨e⟩ := hG.nonempty_iso_directImage_upperStar j j.denseRange
  have h := IsLisse.hasWeightsAtMost_directImage j j.denseRange
    (hG.upperStar j) hw
  intro x
  obtain ⟨E⟩ := nonempty_equiv_stalk_of_iso e x
  exact (h x).of_equiv E

/-- **Purity extends over the missing points.** Let `G` be a lisse Weil sheaf on a smooth
geometrically connected curve `C` over `k₀` and `j : U ↪ C` a dense open immersion such that
`j^*G` is punctually `ι`-pure of weight `w`. Then `G` is punctually `ι`-pure of weight `w` on all
of `C`. By boundary semicontinuity applied to `G ≅ j_* j^* G`
(`AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_of_upperStar`), `G` has weights at most
`w`, and likewise its dual `G^∨`, whose restriction `j^*G^∨` is pure of weight `-w`, has weights
at most `-w`; so the eigenvalues of the local Frobenius of `G` are pure of weight `w`.
(blueprint: `corollary-unramified-boundary-point--2`, consequence clause, subsection
`proposition-weights-j-boundary-points`)
-/
theorem IsLisse.isPunctuallyPureOfWeight_of_upperStar {ι : PadicAlgCl l →+* ℂ}
    {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
    [QuasiCompact j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {G : WeilSheaf k₀ l C} (hG : G.IsLisse) {w : ℝ}
    (hw : ((WeilSheaf.upperStar j).obj G).IsPunctuallyPureOfWeight ι w) :
    G.IsPunctuallyPureOfWeight ι w := by
  have hle := hG.hasWeightsAtMost_of_upperStar j hw.hasWeightsAtMost
  have hdw : ((WeilSheaf.upperStar j).obj (G.dual hG)).IsPunctuallyPureOfWeight ι (-w) := fun z ↦ by
    obtain ⟨E⟩ := nonempty_equiv_stalk_dual hG
      ⟨j.base z.1, Scheme.Hom.map_mem_finitePoints j z.2⟩
    exact (isPureOfWeight_stalk_upperStar_iff j _ z).2
      ((((isPureOfWeight_stalk_upperStar_iff j G z).1 (hw z)).dual).of_equiv E)
  have hle' := hG.dual.hasWeightsAtMost_of_upperStar j hdw.hasWeightsAtMost
  intro x
  obtain ⟨E⟩ := nonempty_equiv_stalk_dual hG x
  exact FrobeniusModule.IsPureOfWeight.of_hasWeightsAtMost_of_equiv_dual E (hle x) (hle' x)

end AlgebraicGeometry.WeilSheaf
