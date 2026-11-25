/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible
public import WeilConjectures.RepresentationTheory.WeilGroupTwist
public import WeilConjectures.WeilSheaf.LisseFiltration

/-!
# Monodromy of irreducible lisse Weil sheaves and Weil II 1.3.14

Let `C₀` be a curve over the finite field `K` with Weil group `W`, base point data `B` and a
monodromy `M` of lisse sheaves on the geometric curve which is an equivalence at the base point
(`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt`), together with the homotopy exact
sequence input `D` (`AlgebraicGeometry.WeilGroup.WeilMonodromyData`). A lisse Weil sheaf `ℱ`
then has a Weil fundamental representation `ρ_ℱ` of `W` on its stalk `ℱ_t`
(`AlgebraicGeometry.WeilGroup.fundamentalRep`).

We show:

* `AlgebraicGeometry.WeilGroup.isIrreducible_fundamentalRep`: if `ℱ` is irreducible lisse, then
  `ρ_ℱ` is an irreducible representation. A `W`-stable subspace `U ⊆ ℱ_t` is the Weil fundamental
  representation of a lisse Weil sheaf `𝒢`, and the inclusion is the stalk of a morphism
  `𝒢 ⟶ ℱ`, which is a monomorphism of Weil sheaves since the stalk functor is faithful and
  lisse sheaves are closed under kernels. Conversely
  (`AlgebraicGeometry.WeilGroup.isIrreducibleLisse_iff_isIrreducible_fundamentalRep`), a lisse
  Weil sheaf with irreducible Weil fundamental representation is irreducible lisse.
* `AlgebraicGeometry.WeilGroup.isBoundedOn_fundamentalRep_geometric`: `ρ_ℱ` is bounded on the
  geometric fundamental group `ker deg`, which is compact and acts continuously.
* `AlgebraicGeometry.WeilGroup.exists_isBoundedOn_twist_fundamentalRep` (**Deligne, Weil II,
  1.3.14**): for irreducible lisse `ℱ` there is `b ∈ ℚ̄_ℓˣ` such that the twist
  `ρ_ℱ ⊗ b^{-deg}` is bounded on all of `W`; and
  `AlgebraicGeometry.WeilGroup.exists_isBoundedOn_fundamentalRep_twist`: this twist is the Weil
  fundamental representation of an irreducible lisse Weil sheaf `ℱ'`, so `ℱ` is the twist of
  an irreducible lisse Weil sheaf with bounded (i.e. integral, "étale") monodromy.
* `AlgebraicGeometry.WeilGroup.exists_finite_range_twist_fundamentalRep`: finite geometric
  monodromy becomes finite monodromy after a twist, and
  `AlgebraicGeometry.WeilGroup.finrank_eq_one_and_exists_twist_eq_one_fundamentalRep`: trivial
  geometric monodromy forces rank one and `ρ_ℱ = b ^ deg`.

For geometrically constant sheaves the sheaf-level statement is
`AlgebraicGeometry.WeilSheaf.exists_iso_constantTwist_of_isGeometricallyConstant`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Representation

section Continuous

variable {k G V : Type*} [NormedField k] [Group G] [AddCommGroup V] [Module k V]

/-- A representation whose matrix coefficients are continuous on a compact subgroup `H` is
bounded on `H`. -/
theorem isBoundedOn_of_isContinuousOn {ρ : Representation k G V} {H : Subgroup G}
    [TopologicalSpace H] [CompactSpace H] (hρ : ρ.IsContinuousOn H.subtype) :
    ρ.IsBoundedOn H := by
  intro v φ
  obtain ⟨C, hC⟩ := (isCompact_range (hρ φ v)).exists_bound_of_continuousOn
    continuous_id.continuousOn
  refine ⟨C, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  exact hC _ ⟨⟨h, hh⟩, rfl⟩

end Continuous

section Subrepresentation

variable {k G H V : Type*} [Field k] [TopologicalSpace k] [Monoid G] [Monoid H]
  [TopologicalSpace H] [AddCommGroup V] [Module k V]

/-- A subrepresentation of a representation continuous along `ι` is continuous along `ι`: a
linear form on the subspace extends to the whole space. -/
theorem IsContinuousOn.subrepresentation {ι : H →* G} {ρ : Representation k G V}
    (hρ : ρ.IsContinuousOn ι) (U : Subrepresentation ρ) : U.toRepresentation.IsContinuousOn ι := by
  intro φ v
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  have (h : H) : φ (U.toRepresentation (ι h) v) = ψ (ρ (ι h) v) := by
    rw [← hψ]
    rfl
  simp_rw [this]
  exact hρ ψ v

end Subrepresentation

section Irreducible

variable {k G V V' : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup V']
  [Module k V']

/-- Irreducibility is transported along an intertwining linear equivalence. -/
theorem IsIrreducible.of_linearEquiv {ρ : Representation k G V} {ρ' : Representation k G V'}
    [ρ.IsIrreducible] (e : V' ≃ₗ[k] V) (he : ∀ g v, e (ρ' g v) = ρ g (e v)) :
    ρ'.IsIrreducible := by
  obtain ⟨hV, h⟩ := isIrreducible_iff.1 ‹ρ.IsIrreducible›
  refine isIrreducible_iff.2 ⟨e.symm.injective.nontrivial, fun U hU ↦ ?_⟩
  have hU' := h (U.map e.toLinearMap) fun g v hv ↦ by
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨ρ' g u, hU g u hu, he g u⟩
  rw [← Submodule.comap_map_eq_of_injective e.injective U]
  refine hU'.imp (fun h₀ ↦ ?_) fun h₀ ↦ ?_
  · rw [h₀, Submodule.comap_bot]
    exact LinearEquiv.ker _
  · rw [h₀, Submodule.comap_top]

/-- The twist of an irreducible representation by a character is irreducible: both have the same
invariant subspaces. -/
theorem IsIrreducible.twist {ρ : Representation k G V} [ρ.IsIrreducible] (χ : G →* kˣ) :
    (ρ.twist χ).IsIrreducible := by
  obtain ⟨hV, h⟩ := isIrreducible_iff.1 ‹ρ.IsIrreducible›
  refine isIrreducible_iff.2 ⟨hV, fun U hU ↦ h U fun g v hv ↦ ?_⟩
  have : ρ g v = ((χ g : kˣ) : k)⁻¹ • ρ.twist χ g v := by
    rw [twist_apply, LinearMap.smul_apply, inv_smul_smul₀ (Units.ne_zero _)]
  rw [this]
  exact U.smul_mem _ (hU g v hv)

end Irreducible

end Representation

namespace AlgebraicGeometry.WeilGroup

open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  [IsCurve (C ↘ Spec (.of K))] {W : WeilGroup (C ↘ Spec (.of K))}
  {M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K} {B : BasePointData W}

section StalkMap

/-- The stalk map of the zero morphism is zero. -/
lemma stalkMap_zero {F G : WeilSheaf K l C} (hF : F.IsLisse) (hG : G.IsLisse) :
    stalkMap (B := B) (0 : F ⟶ G) hF hG = 0 := by
  have h₁ : WeilSheaf.toLisseMap (0 : F ⟶ G) hF hG = 0 := rfl
  have : (lisseStalk l B.t).Additive := inferInstance
  have : (WeilCoefficients.toModuleCat.{u} l).Additive := inferInstance
  simp only [stalkMap, h₁, Functor.map_zero]
  rfl

end StalkMap

section Irreducible

variable (M)

/-- The stalk at the base point of a zero lisse Weil sheaf is zero. -/
lemma subsingleton_stalk_of_isZero {F : WeilSheaf K l C} (hF : F.IsLisse) (h : IsZero F) :
    Subsingleton (LisseMonodromy.StalkSpace B.t (F.toLisse hF)) := by
  refine subsingleton_of_forall_eq 0 fun v ↦ ?_
  have h' := LinearMap.congr_fun (stalkMap_id (B := B) hF) v
  rw [h.eq_of_src (𝟙 F) 0, stalkMap_zero] at h'
  exact h'.symm

/-- A lisse Weil sheaf whose stalk at the base point is zero is zero, if the monodromy at the
base point is an equivalence. -/
lemma isZero_of_subsingleton_stalk (hM : M.IsEquivalenceAt B.t) {F : WeilSheaf K l C}
    (hF : F.IsLisse) [Subsingleton (LisseMonodromy.StalkSpace B.t (F.toLisse hF))] :
    IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  have h := stalkMap_injective M hM (X := ⟨F, hF⟩) (Y := ⟨F, hF⟩) (𝟙 _)
    (ObjectProperty.homMk 0) (LinearMap.ext fun v ↦ by
      rw [Subsingleton.elim v 0, map_zero, map_zero])
  exact congrArg (fun f ↦ f.hom) h

/-- A morphism of lisse Weil sheaves whose stalk at the base point is injective is a
monomorphism of Weil sheaves, if the monodromy at the base point is an equivalence: its kernel is
lisse, with zero stalk map to the source, hence zero. -/
theorem mono_of_injective_stalkMap (hM : M.IsEquivalenceAt B.t) {F G : WeilSheaf K l C}
    (hF : F.IsLisse) (hG : G.IsLisse) (φ : F ⟶ G)
    (hφ : Function.Injective (stalkMap (B := B) φ hF hG)) : Mono φ := by
  have hK := (WeilSheaf.IsLisse.kernel_cokernel hF hG φ).1
  refine Preadditive.mono_of_kernel_zero ?_
  have h := stalkMap_injective M hM (X := ⟨kernel φ, hK⟩) (Y := ⟨F, hF⟩)
    (ObjectProperty.homMk (kernel.ι φ)) (ObjectProperty.homMk 0) (LinearMap.ext fun v ↦ by
      apply hφ
      have h₁ := LinearMap.congr_fun (stalkMap_comp (B := B) (kernel.ι φ) φ hK hF hG) v
      rw [kernel.condition, stalkMap_zero] at h₁
      simp only [ObjectProperty.homMk_hom, stalkMap_zero, LinearMap.zero_apply, map_zero]
      exact h₁.symm)
  exact congrArg (fun f ↦ f.hom) h

/-- **The Weil fundamental representation of an irreducible lisse Weil sheaf is irreducible**
(cf. Deligne, Weil II, 1.3.14 and `situation-weil`). A `W`-stable subspace
`U` of the stalk `ℱ_t` is the Weil fundamental representation of a lisse Weil sheaf `𝒢`, and the
inclusion `U ⊆ ℱ_t` is the stalk of a monomorphism `𝒢 ⟶ ℱ`; by irreducibility `𝒢` is zero or
`𝒢 ⟶ ℱ` is an isomorphism, i.e. `U = 0` or `U = ℱ_t`. -/
theorem isIrreducible_fundamentalRep (D : WeilMonodromyData B) (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l C} (hF : F.IsIrreducibleLisse) :
    (fundamentalRep M D F hF.1).IsIrreducible := by
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) :=
    F.finiteDimensional_stalkObj B.t
  refine Representation.isIrreducible_iff.2 ⟨?_, fun U hU ↦ ?_⟩
  · rw [← not_subsingleton_iff_nontrivial]
    intro h
    exact hF.2.1 (isZero_of_subsingleton_stalk M hM hF.1)
  let U' : Subrepresentation (fundamentalRep M D F hF.1) := ⟨U, fun g v hv ↦ hU g v hv⟩
  obtain ⟨X, e, he⟩ := exists_fundamentalRep_linearEquiv D hM U U'.toRepresentation
    ((fundamentalRep_isContinuousOn D F hF.1 hM).subrepresentation U')
  obtain ⟨f, hf⟩ := exists_stalkMap_eq D hM (Y := ⟨F, hF.1⟩) (U.subtype ∘ₗ e.toLinearMap)
    fun w v ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he]
      rfl
  have hinj : Function.Injective (stalkMap (B := B) f.hom X.property hF.1) := by
    rw [hf]
    exact U.injective_subtype.comp e.injective
  have := mono_of_injective_stalkMap M hM X.property hF.1 f.hom hinj
  rcases hF.2.2 X.obj f.hom this X.property with h | h
  · left
    have := subsingleton_stalk_of_isZero (B := B) X.property h
    rw [eq_bot_iff]
    intro v hv
    have h₀ : (⟨v, hv⟩ : U) = 0 := by
      rw [← e.apply_symm_apply ⟨v, hv⟩, Subsingleton.elim (e.symm ⟨v, hv⟩) 0, map_zero]
    simpa using congrArg Subtype.val h₀
  · right
    rw [eq_top_iff]
    intro v _
    have h₁ := LinearMap.congr_fun (stalkMap_comp (B := B) (inv f.hom) f.hom hF.1 X.property hF.1) v
    rw [IsIso.inv_hom_id, stalkMap_id, hf, LinearMap.id_apply] at h₁
    rw [h₁]
    exact Submodule.coe_mem _

/-- Conversely, a lisse Weil sheaf whose Weil fundamental representation is irreducible is
irreducible lisse. The image of the stalk of a lisse Weil subsheaf `i : 𝒢 ⟶ ℱ` is a `W`-stable
subspace; if it is zero then `i = 0` by faithfulness, so `𝒢 = 0`, and if it is everything then
the (lisse) cokernel of `i` has zero stalk map, so `i` is an epimorphism, hence an isomorphism. -/
theorem isIrreducibleLisse_of_isIrreducible_fundamentalRep (D : WeilMonodromyData B)
    (hM : M.IsEquivalenceAt B.t) {F : WeilSheaf K l C} (hF : F.IsLisse)
    (h : (fundamentalRep M D F hF).IsIrreducible) : F.IsIrreducibleLisse := by
  obtain ⟨hnt, hirr⟩ := Representation.isIrreducible_iff.1 h
  refine ⟨hF, fun hz ↦ ?_, fun G i hi hG ↦ ?_⟩
  · have := subsingleton_stalk_of_isZero (B := B) hF hz
    exact not_subsingleton _ this
  rcases hirr (LinearMap.range (stalkMap (B := B) i hG hF)) (fun g v hv ↦ by
      obtain ⟨u, rfl⟩ := hv
      exact ⟨_, stalkMap_fundamentalRep D i hG hF g u⟩) with h₀ | h₀
  · left
    obtain rfl : i = 0 := congrArg (fun f ↦ f.hom) (stalkMap_injective M hM (X := ⟨G, hG⟩)
      (Y := ⟨F, hF⟩) (ObjectProperty.homMk i) (ObjectProperty.homMk 0)
      ((LinearMap.range_eq_bot.1 h₀).trans (stalkMap_zero (B := B) hG hF).symm))
    exact IsZero.of_mono_zero G F
  · right
    have hQ := (WeilSheaf.IsLisse.kernel_cokernel hG hF i).2
    have hπ : cokernel.π i = 0 := congrArg (fun f ↦ f.hom) (stalkMap_injective M hM
      (X := ⟨F, hF⟩) (Y := ⟨cokernel i, hQ⟩) (ObjectProperty.homMk (cokernel.π i))
      (ObjectProperty.homMk 0) (LinearMap.ext fun v ↦ by
        obtain ⟨u, rfl⟩ := LinearMap.range_eq_top.1 h₀ v
        have h₁ := LinearMap.congr_fun (stalkMap_comp (B := B) i (cokernel.π i) hG hF hQ) u
        rw [cokernel.condition, stalkMap_zero] at h₁
        simp only [ObjectProperty.homMk_hom, stalkMap_zero, LinearMap.zero_apply]
        exact h₁.symm))
    have : Epi i := Preadditive.epi_of_cokernel_zero hπ
    exact isIso_of_mono_of_epi i

/-- A lisse Weil sheaf is irreducible lisse if and only if its Weil fundamental representation is
irreducible. -/
theorem isIrreducibleLisse_iff_isIrreducible_fundamentalRep (D : WeilMonodromyData B)
    (hM : M.IsEquivalenceAt B.t) {F : WeilSheaf K l C} (hF : F.IsLisse) :
    F.IsIrreducibleLisse ↔ (fundamentalRep M D F hF).IsIrreducible :=
  ⟨fun h ↦ isIrreducible_fundamentalRep M D hM h,
    isIrreducibleLisse_of_isIrreducible_fundamentalRep M D hM hF⟩

end Irreducible

section Twist

variable (M) (D : WeilMonodromyData B)

open Representation in
/-- The Weil fundamental representation is bounded on the geometric fundamental group
`ker deg`: it acts continuously and `ker deg` is compact. -/
theorem isBoundedOn_fundamentalRep_geometric (hM : M.IsEquivalenceAt B.t) (F : WeilSheaf K l C)
    (hF : F.IsLisse) : (fundamentalRep M D F hF).IsBoundedOn W.geometric :=
  isBoundedOn_of_isContinuousOn (fundamentalRep_isContinuousOn D F hF hM)

open Representation in
/-- **Deligne, Weil II, 1.3.14**, for the Weil fundamental representation: if `ℱ` is an
irreducible lisse Weil sheaf, there is `b ∈ ℚ̄_ℓˣ` such that the twist `ρ_ℱ ⊗ b^{-deg}` of its
Weil fundamental representation is bounded on the whole Weil group. -/
theorem exists_isBoundedOn_twist_fundamentalRep (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l C} (hF : F.IsIrreducibleLisse) :
    ∃ b : (PadicAlgCl l)ˣ,
      ((fundamentalRep M D F hF.1).twist (degreeCharacter W.deg b⁻¹)).IsBoundedOn Set.univ := by
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) :=
    F.finiteDimensional_stalkObj B.t
  have := isIrreducible_fundamentalRep M D hM hF
  exact exists_isBoundedOn_twist _ W.deg_surjective
    (isBoundedOn_fundamentalRep_geometric M D hM F hF.1)

open Representation in
/-- **Finite geometric monodromy** (cf. Deligne, Weil II, 1.3.14): if the geometric monodromy
group of an irreducible lisse Weil sheaf `ℱ` is finite, then a twist `ρ_ℱ ⊗ b^{-deg}` of its
Weil fundamental representation has finite image. -/
theorem exists_finite_range_twist_fundamentalRep (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l C} (hF : F.IsIrreducibleLisse)
    (hfin : (fundamentalRep M D F hF.1 '' W.geometric).Finite) :
    ∃ b : (PadicAlgCl l)ˣ,
      (Set.range ((fundamentalRep M D F hF.1).twist (degreeCharacter W.deg b⁻¹))).Finite := by
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) :=
    F.finiteDimensional_stalkObj B.t
  have := isIrreducible_fundamentalRep M D hM hF
  exact exists_finite_range_twist _ W.deg_surjective hfin

open Representation in
/-- **Trivial geometric monodromy**: if the geometric fundamental group acts trivially on the
stalk of an irreducible lisse Weil sheaf `ℱ`, then `ℱ` has rank one and its Weil fundamental
representation is a character `b ^ deg`. -/
theorem finrank_eq_one_and_exists_twist_eq_one_fundamentalRep (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l C} (hF : F.IsIrreducibleLisse)
    (htriv : ∀ g, M.rep B.t (F.toLisse hF.1) g = 1) :
    Module.finrank (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) = 1 ∧
      ∃ b : (PadicAlgCl l)ˣ,
        ∀ w, (fundamentalRep M D F hF.1).twist (degreeCharacter W.deg b⁻¹) w = 1 := by
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) :=
    F.finiteDimensional_stalkObj B.t
  have := isIrreducible_fundamentalRep M D hM hF
  refine finrank_eq_one_and_exists_twist_eq_one _ W.deg_surjective fun i hi ↦ ?_
  rw [fundamentalRep_geometric M D F hF.1 ⟨i, hi⟩]
  exact htriv _

open Representation in
/-- **Deligne, Weil II, 1.3.14**, sheaf-theoretic form: an irreducible lisse Weil sheaf `ℱ` is
the twist of a lisse Weil sheaf `ℱ'` with bounded monodromy. Precisely, there are `b ∈ ℚ̄_ℓˣ`, a
lisse Weil sheaf `ℱ'` whose Weil fundamental representation is bounded on the whole Weil group,
and an identification `ℱ'_t ≅ ℱ_t` of stalks carrying the Weil fundamental representation of
`ℱ'` to the twist `ρ_ℱ ⊗ b^{-deg}`; moreover `ℱ'` is again irreducible lisse. -/
theorem exists_isBoundedOn_fundamentalRep_twist (hM : M.IsEquivalenceAt B.t)
    {F : WeilSheaf K l C} (hF : F.IsIrreducibleLisse) :
    ∃ (b : (PadicAlgCl l)ˣ) (X : LisseWeilSheaf K l C)
      (e : LisseMonodromy.StalkSpace B.t (X.obj.toLisse X.property) ≃ₗ[PadicAlgCl l]
        LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)),
      (∀ w v, e (fundamentalRep M D X.obj X.property w v) =
        (fundamentalRep M D F hF.1).twist (degreeCharacter W.deg b⁻¹) w (e v)) ∧
      X.obj.IsIrreducibleLisse ∧ (fundamentalRep M D X.obj X.property).IsBoundedOn Set.univ := by
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF.1)) :=
    F.finiteDimensional_stalkObj B.t
  obtain ⟨b, hb⟩ := exists_isBoundedOn_twist_fundamentalRep M D hM hF
  set σ := (fundamentalRep M D F hF.1).twist (degreeCharacter W.deg b⁻¹)
  have hσ : σ.IsContinuousOn W.geometric.subtype := by
    intro φ v
    have h (u : W.geometric) : φ (σ (W.geometric.subtype u) v) =
        φ (fundamentalRep M D F hF.1 (W.geometric.subtype u) v) := by
      simp [σ, MonoidHom.mem_ker.1 u.2]
    simp_rw [h]
    exact fundamentalRep_isContinuousOn D F hF.1 hM φ v
  obtain ⟨X, e, he⟩ := exists_fundamentalRep_linearEquiv D hM _ σ hσ
  have := isIrreducible_fundamentalRep M D hM hF
  have : σ.IsIrreducible := IsIrreducible.twist _
  refine ⟨b, X, e, he, isIrreducibleLisse_of_isIrreducible_fundamentalRep M D hM X.property
    (IsIrreducible.of_linearEquiv e he), fun v φ ↦ ?_⟩
  obtain ⟨c, hc⟩ := hb (e v) (φ ∘ₗ e.symm.toLinearMap)
  refine ⟨c, ?_⟩
  rintro _ ⟨w, -, rfl⟩
  have h := hc _ ⟨w, Set.mem_univ _, rfl⟩
  beta_reduce at h
  rwa [LinearMap.comp_apply, ← he, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h

end Twist

open Representation in
/-- **Deligne, Weil II, 1.3.14** for the Weil fundamental representation at base point data `B`,
with the homotopy exact sequence data `B.weilMonodromyData`: for an irreducible lisse Weil sheaf
`ℱ` some twist `ρ_ℱ ⊗ b^{-deg}` is bounded on the whole Weil group. -/
theorem BasePointData.exists_isBoundedOn_twist_fundamentalRep (B : BasePointData W)
    (hM : M.IsEquivalenceAt B.t) {F : WeilSheaf K l C} (hF : F.IsIrreducibleLisse) :
    ∃ b : (PadicAlgCl l)ˣ, ((fundamentalRep M B.weilMonodromyData F hF.1).twist
      (degreeCharacter W.deg b⁻¹)).IsBoundedOn Set.univ :=
  WeilGroup.exists_isBoundedOn_twist_fundamentalRep M _ hM hF

end AlgebraicGeometry.WeilGroup
