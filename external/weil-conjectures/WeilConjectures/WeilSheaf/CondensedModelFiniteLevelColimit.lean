/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix
public import WeilConjectures.WeilSheaf.CondensedModelFiniteLevel

/-!
# The geometric fibre as the limit of the finite levels

Let `k` be a field, `f : X₀ ⟶ Spec k`, `k̄ = AlgebraicClosure k` and `X̄ = X₀ ⊗_k k̄` the geometric
fibre, with projection `p : X̄ ⟶ X₀`. For a finite subextension `K` of `k̄ / k` let
`X₀ ⊗_k K` be the finite level and `ι_K : X̄ ⟶ X₀ ⊗_k K`, `q_K : X₀ ⊗_k K ⟶ X₀` the projections
(`WeilConjectures.WeilSheaf.CondensedModelFiniteLevel`). This file supplies the profinite step of
the descent of `Fr`-invariant morphisms along `p`, for the constant `ℓ`-adic sheaf `ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.adicConstantSheaf`, whose sections over `V` are the locally finite
continuous functions `V → ℚ̄_ℓ`) and for finite free `ℚ̄_ℓ`-modules.

1. **Limits.** Over a cofiltered diagram of quasi-compact quasi-separated schemes with affine
   transition maps, open and closed subsets and locally constant functions of the limit come from
   a finite stage (`AlgebraicGeometry.exists_isClopen_preimage_eq_of_isLimit`,
   `AlgebraicGeometry.exists_isLocallyConstant_comp_eq_of_isLimit`).
2. **The geometric fibre is the limit of the finite levels**: `X̄ = lim_K X₀ ⊗_k K`
   (`AlgebraicGeometry.Scheme.Hom.isLimitFiniteLevelCone`), base changing
   `Spec k̄ = lim_K Spec K` (`AlgebraicGeometry.FiniteIntermediateField.isLimitSpecCone`).
3. **Sections.** If `X₀` is quasi-compact and quasi-separated and `X̄` is locally connected (e.g.
   `X₀` of finite type over `k`, `AlgebraicGeometry.Scheme.Hom.isLocallyNoetherian_geometricFiber`),
   then `Γ(X̄, ℚ̄_ℓ) = colim_K Γ(X₀ ⊗_k K, ℚ̄_ℓ)`
   (`AlgebraicGeometry.Scheme.Hom.isColimitAdicFunctionsPresheafMapCoconeFiniteLevelCone`,
   `AlgebraicGeometry.Scheme.Hom.exists_locallyFiniteFunctionsComp_geometricFiberToFiniteLevel_eq`):
   a section is continuous with values in the totally disconnected `ℚ̄_ℓ`, hence locally constant
   on the locally connected `X̄`, hence defined at a finite level.
4. **Frobenius invariants.** For `k` finite, `H⁰(X̄, ℚ̄_ℓ)^{Fr} = H⁰(X₀, ℚ̄_ℓ)`
   (`AlgebraicGeometry.Scheme.Hom.exists_locallyFiniteFunctionsComp_geometricFiberProj_eq`,
   `AlgebraicGeometry.Scheme.Hom.locallyFiniteFunctionsComp_geometricFiberProj_injective`): an
   `Fr`-invariant section is defined at a finite level, where it is invariant under the Galois
   action of the powers of `Fr_K`; hence it is constant on the fibres of `p` and descends along
   the quotient map `p`.
5. **Finite free modules.** For `k` finite, an `Fr`-invariant morphism
   `ℚ̄_ℓ,X̄^ι ⟶ ℚ̄_ℓ,X̄^κ` is the pullback of a unique morphism `ℚ̄_ℓ,X₀^ι ⟶ ℚ̄_ℓ,X₀^κ`
   (`AlgebraicGeometry.ProEtale.AdicSheaf.exists_freeUpperStarIso_geometricFiberProj_eq`,
   `AlgebraicGeometry.ProEtale.AdicSheaf.freeUpperStarIso_conj_injective`), by applying 4 to the
   entries of its matrix (`AlgebraicGeometry.ProEtale.AdicSheaf.unitMatrix_adicUpperStar`).
6. **The condensed model.** For `k` finite, the same holds for the condensed coefficient ring
   `Λ_X₀ = p_X₀^* ℚ̄_ℓ` (`AlgebraicGeometry.ProEtale.condensedRingObj`), evaluated on the objects
   `X̄ ⟶ X₀` and `X₀ ⊗_k K ⟶ X₀` of the pro-étale site of `X₀`:
   `Λ_X₀(X̄) = colim_K Λ_X₀(X₀ ⊗_k K)`
   (`AlgebraicGeometry.Scheme.Hom.isColimitCondensedRingObjMapCoconeFiniteLevelProEtCone`) and
   `Λ_X₀(X̄)^{Fr} = Λ_X₀(X₀)`
   (`AlgebraicGeometry.Scheme.Hom.exists_condensedRingObj_map_geometricFiberProjProEt_eq`),
   by transport along `Λ_X₀ ≅ ℚ̄_ℓ,X₀` (`AlgebraicGeometry.ProEtale.condensedRingObjIsoForgetAb`).

The hypothesis that `X̄` is locally connected cannot be dropped: for a finite field `k` and
`X₀ = Spec k̄`, the geometric fibre is the profinite space `Spec (k̄ ⊗_k k̄) ≅ Gal(k̄ / k)`, on
which a continuous function to `ℚ_ℓ` need not factor through a finite quotient.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Topology


/-- A continuous map from a locally connected space to a totally disconnected space is locally
constant. -/
lemma Continuous.isLocallyConstant {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace X] [TotallyDisconnectedSpace Y] {g : X → Y} (hg : Continuous g) :
    IsLocallyConstant g :=
  IsLocallyConstant.of_constant_on_connected_components fun x y hy ↦
    (hg.image_connectedComponent_eq_singleton x).subset ⟨y, hy, rfl⟩

/-- Pulling back locally finite `ℓ`-adic functions along a surjective continuous map is
injective. -/
lemma PadicAlgCl.locallyFiniteFunctionsComp_injective {l : ℕ} [Fact l.Prime] {T T' : Type*}
    [TopologicalSpace T] [TopologicalSpace T'] (g : C(T', T)) (hg : Function.Surjective g) :
    Function.Injective (PadicAlgCl.locallyFiniteFunctionsComp l g) := by
  intro s₁ s₂ h
  refine Subtype.ext (ContinuousMap.ext fun y ↦ ?_)
  obtain ⟨x, rfl⟩ := hg y
  exact ContinuousMap.congr_fun (congrArg Subtype.val h) x

namespace AlgebraicGeometry

section Limit

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

include hc in
/-- **Open and closed subsets of a limit come from a finite stage.** Let `{Dᵢ}` be a cofiltered
diagram of quasi-compact quasi-separated schemes with affine transition maps. Every open and
closed subset `C` of `lim Dᵢ` is the preimage of an open and closed subset of some `Dᵢ`: `C` and
its complement are quasi-compact opens, hence preimages of quasi-compact opens of some stage, and
at a later stage these are disjoint and cover (Stacks Project, Tag 01Z4). -/
lemma exists_isClopen_preimage_eq_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {C : Set c.pt} (hC : IsClopen C) :
    ∃ (i : I) (V : Set (D.obj i)), IsClopen V ∧ c.π.app i ⁻¹' V = C := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let U : c.pt.Opens := ⟨C, hC.isOpen⟩
  let U' : c.pt.Opens := ⟨Cᶜ, hC.isClosed.isOpen_compl⟩
  obtain ⟨i, V, hV, hVU⟩ := exists_preimage_eq D c hc U hC.isClosed.isCompact
  obtain ⟨j, V', hV', hVU'⟩ := exists_preimage_eq D c hc U' hC.isOpen.isClosed_compl.isCompact
  obtain ⟨k, fki, fkj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  let A := D.map fki ⁻¹ᵁ V
  let B := D.map fkj ⁻¹ᵁ V'
  have hA : c.π.app k ⁻¹ᵁ A = U := by rw [← Scheme.Hom.comp_preimage, c.w, hVU]
  have hB : c.π.app k ⁻¹ᵁ B = U' := by rw [← Scheme.Hom.comp_preimage, c.w, hVU']
  have hAc : IsCompact (A : Set (D.obj k)) := QuasiCompact.isCompact_preimage _ V.2 hV
  have hBc : IsCompact (B : Set (D.obj k)) := QuasiCompact.isCompact_preimage _ V'.2 hV'
  obtain ⟨l, flk, hl⟩ := exists_map_preimage_eq_map_preimage D c hc (U := A ⊓ B) (V := ⊥)
    (QuasiSeparatedSpace.inter_isCompact _ _ A.2 hAc B.2 hBc) isCompact_empty (by
      rw [Scheme.Hom.preimage_inf, hA, hB, Scheme.Hom.preimage_bot]
      ext x
      simp [U, U'])
  obtain ⟨l', fl'k, hl'⟩ := exists_map_preimage_eq_map_preimage D c hc (U := A ⊔ B) (V := ⊤)
    (hAc.union hBc) isCompact_univ (by
      rw [Scheme.Hom.preimage_sup, hA, hB, Scheme.Hom.preimage_top]
      ext x
      simp [U, U'])
  obtain ⟨m, a, b, hab⟩ := IsCofiltered.cospan flk fl'k
  let W := D.map (a ≫ flk) ⁻¹ᵁ A
  let W' := D.map (a ≫ flk) ⁻¹ᵁ B
  have hinf : W ⊓ W' = ⊥ := by
    simp only [W, W', Functor.map_comp, Scheme.Hom.comp_preimage, ← Scheme.Hom.preimage_inf, hl,
      Scheme.Hom.preimage_bot]
  have hsup : W ⊔ W' = ⊤ := by
    simp only [W, W', hab, Functor.map_comp, Scheme.Hom.comp_preimage, ← Scheme.Hom.preimage_sup,
      hl', Scheme.Hom.preimage_top]
  have hW : IsClopen (W : Set (D.obj m)) := by
    refine ⟨⟨?_⟩, W.2⟩
    convert W'.2 using 1
    ext x
    have h1 := congrArg (x ∈ ·) hinf
    have h2 := congrArg (x ∈ ·) hsup
    simp only [TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_sup, eq_iff_iff] at h1 h2
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    tauto
  refine ⟨m, W, hW, ?_⟩
  have : c.π.app m ⁻¹ᵁ W = U := by
    simp only [W, ← Scheme.Hom.comp_preimage, c.w, hA]
  exact congrArg (fun O : c.pt.Opens ↦ (O : Set c.pt)) this

include hc in
/-- **Locally constant functions on a limit come from a finite stage.** Let `{Dᵢ}` be a
cofiltered diagram of quasi-compact quasi-separated schemes with affine transition maps. Every
locally constant function `g` on `lim Dᵢ` is of the form `g' ∘ πᵢ` for a locally constant
function `g'` on some stage `Dᵢ`: the finitely many fibres of `g` are open and closed, hence come
from a common stage (`AlgebraicGeometry.exists_isClopen_preimage_eq_of_isLimit`). -/
lemma exists_isLocallyConstant_comp_eq_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {α : Type*} [Nonempty α] {g : c.pt → α}
    (hg : IsLocallyConstant g) :
    ∃ (i : I) (g' : D.obj i → α), IsLocallyConstant g' ∧ g' ∘ c.π.app i = g := by
  classical
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : Finite (Set.range g) := hg.range_finite
  have := Fintype.ofFinite (Set.range g)
  choose i V hV hVC using fun a : Set.range g ↦
    exists_isClopen_preimage_eq_of_isLimit D c hc (hg.isClopen_fiber (a : α))
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let fj (a : Set.range g) : j ⟶ i a :=
    (hj (Finset.mem_image_of_mem _ (Finset.mem_univ a))).some
  let W (a : Set.range g) : Set (D.obj j) := D.map (fj a) ⁻¹' V a
  have hW (a : Set.range g) : IsClopen (W a) := (hV a).preimage (D.map (fj a)).continuous
  have hWC (a : Set.range g) (x : c.pt) : c.π.app j x ∈ W a ↔ g x = a := by
    simp only [W, Set.mem_preimage]
    rw [← Scheme.Hom.comp_apply, c.w]
    exact Set.ext_iff.mp (hVC a) x
  let P (y : D.obj j) : Set (Set.range g) := {a | y ∈ W a}
  let F (S : Set (Set.range g)) : α := if h : S.Nonempty then (h.some : α) else
    Classical.arbitrary α
  have hP : IsLocallyConstant P := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have : ∀ᶠ z in 𝓝 y, ∀ a, (z ∈ W a ↔ y ∈ W a) := by
      rw [Filter.eventually_all]
      intro a
      by_cases hy : y ∈ W a
      · filter_upwards [(hW a).isOpen.mem_nhds hy] with z hz
        simp [hz, hy]
      · filter_upwards [(hW a).compl.isOpen.mem_nhds hy] with z hz
        simp only [Set.mem_compl_iff] at hz
        simp [hz, hy]
    filter_upwards [this] with z hz
    exact Set.ext fun a ↦ hz a
  refine ⟨j, F ∘ P, hP.comp F, funext fun x ↦ ?_⟩
  have hPx : P (c.π.app j x) = {⟨g x, x, rfl⟩} := by
    ext a
    simp only [P, Set.mem_ofPred_eq, Set.mem_singleton_iff, hWC]
    rw [Subtype.ext_iff]
    exact eq_comm
  have hne : (P (c.π.app j x)).Nonempty := by
    rw [hPx]
    exact Set.singleton_nonempty _
  have key (S : Set (Set.range g)) (h : S.Nonempty) (b : Set.range g) (hS : S = {b}) :
      (h.some : α) = b := by
    subst hS
    exact congrArg _ (Set.mem_singleton_iff.mp h.some_mem)
  simp only [Function.comp_apply, F, dite_eq_left hne]
  exact key _ hne _ hPx

end Limit

namespace FiniteIntermediateField

variable {k ks : Type u} [Field k] [Field ks] [Algebra k ks]

/-- The transition map `Spec K ⟶ Spec K` of `K ≤ K` is the identity. -/
lemma specMap_refl (K : FiniteIntermediateField k ks) : specMap (le_refl K) = 𝟙 _ :=
  (specDiagram k ks).map_id (Opposite.op K)

/-- The transition maps `Spec K' ⟶ Spec K` compose. -/
@[reassoc]
lemma specMap_comp_specMap {K K' K'' : FiniteIntermediateField k ks} (h : K ≤ K')
    (h' : K' ≤ K'') : specMap h' ≫ specMap h = specMap (h.trans h') :=
  ((specDiagram k ks).map_comp (homOfLE h').op (homOfLE h).op).symm

end FiniteIntermediateField

namespace Scheme.Hom

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

open FiniteIntermediateField

/-- For a finite subextension `K` of `k̄ / k`, the embedding `K ↪ k̄` induces on spectra the
projection `Spec k̄ ⟶ Spec K` of the limit cone. -/
lemma spec_map_val (K : FiniteIntermediateField k (AlgebraicClosure k)) :
    Spec.map (CommRingCat.ofHom K.1.val.toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap K.1 (AlgebraicClosure k))) :=
  rfl

/-- The finite level `X₀ ⊗_k K` is the fibre product `X₀ ×_{Spec k} Spec K`. -/
lemma isPullback_finiteLevel (K : Type u) [Field K] [Algebra k K] :
    IsPullback (f.finiteLevelProj K) (f.finiteLevelToSpec K) f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  IsPullback.of_hasPullback _ _

/-- The geometric fibre `X̄` is the fibre product `X₀ ×_{Spec k} Spec k̄`. -/
lemma isPullback_geometricFiber :
    IsPullback f.geometricFiberProj f.geometricFiberToAlgebraicClosure f
      (Scheme.specAlgebraicClosure k).hom :=
  IsPullback.of_hasPullback _ _

/-- The transition map `X₀ ⊗_k K' ⟶ X₀ ⊗_k K` for finite subextensions `K ≤ K'` of `k̄ / k`. -/
def finiteLevelMap {K K' : FiniteIntermediateField k (AlgebraicClosure k)} (h : K ≤ K') :
    f.finiteLevel K'.1 ⟶ f.finiteLevel K.1 :=
  pullback.map _ _ _ _ (𝟙 X₀) (specMap h) (𝟙 _) (by simp) (by
    rw [Category.comp_id, ← Spec.map_comp]
    rfl)

/-- The transition maps of the finite levels lie over `X₀`. -/
@[reassoc (attr := simp)]
lemma finiteLevelMap_comp_finiteLevelProj {K K' : FiniteIntermediateField k (AlgebraicClosure k)}
    (h : K ≤ K') : f.finiteLevelMap h ≫ f.finiteLevelProj K.1 = f.finiteLevelProj K'.1 := by
  simp [finiteLevelMap, finiteLevelProj]

/-- The transition maps of the finite levels lie over the transition maps of `Spec K`. -/
@[reassoc (attr := simp)]
lemma finiteLevelMap_comp_finiteLevelToSpec
    {K K' : FiniteIntermediateField k (AlgebraicClosure k)} (h : K ≤ K') :
    f.finiteLevelMap h ≫ f.finiteLevelToSpec K.1 = f.finiteLevelToSpec K'.1 ≫ specMap h := by
  simp [finiteLevelMap, finiteLevelToSpec]

/-- The cofiltered diagram `K ↦ X₀ ⊗_k K` of the finite levels, over the finite subextensions
`K` of `k̄ / k`. -/
@[simps]
def finiteLevelDiagram : (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ ⥤ Scheme.{u} where
  obj K := f.finiteLevel K.unop.1
  map g := f.finiteLevelMap (leOfHom g.unop)
  map_id K := f.finiteLevel_hom_ext _ (by simp) (by
    rw [finiteLevelMap_comp_finiteLevelToSpec, specMap_refl]
    simp)
  map_comp g g' := f.finiteLevel_hom_ext _ (by simp) (by
    rw [finiteLevelMap_comp_finiteLevelToSpec, Category.assoc,
      finiteLevelMap_comp_finiteLevelToSpec, finiteLevelMap_comp_finiteLevelToSpec_assoc,
      specMap_comp_specMap])

/-- The structure morphisms `X₀ ⊗_k K ⟶ Spec K`, as a morphism of diagrams. -/
@[simps]
def finiteLevelDiagramToSpec : f.finiteLevelDiagram ⟶ specDiagram k (AlgebraicClosure k) where
  app K := f.finiteLevelToSpec K.unop.1
  naturality _ _ g := by simp

/-- The geometric fibre `X̄ = X₀ ⊗_k k̄`, as a cone over the finite levels. -/
@[simps pt]
def finiteLevelCone : Cone f.finiteLevelDiagram where
  pt := f.geometricFiber
  π := { app K := f.geometricFiberToFiniteLevel K.unop.1.val
         naturality _ _ g := f.finiteLevel_hom_ext _ (by simp) (by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            finiteLevelDiagram_map, Category.assoc,
            finiteLevelMap_comp_finiteLevelToSpec,
            geometricFiberToFiniteLevel_comp_finiteLevelToSpec,
            geometricFiberToFiniteLevel_comp_finiteLevelToSpec_assoc, spec_map_val,
            specCone_π_app_specMap]) }

@[simp]
lemma finiteLevelCone_π_app (K : (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ) :
    f.finiteLevelCone.π.app K = f.geometricFiberToFiniteLevel K.unop.1.val :=
  rfl

/-- The square `X̄ ⟶ X₀ ⊗_k K ⟶ Spec K`, `X̄ ⟶ Spec k̄ ⟶ Spec K` is cartesian. -/
lemma isPullback_geometricFiberToFiniteLevel
    (K : FiniteIntermediateField k (AlgebraicClosure k)) :
    IsPullback (f.geometricFiberToFiniteLevel K.1.val) f.geometricFiberToAlgebraicClosure
      (f.finiteLevelToSpec K.1) (Spec.map (CommRingCat.ofHom (algebraMap K.1 _))) := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap K.1 (AlgebraicClosure k))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K.1)) = (Scheme.specAlgebraicClosure k).hom := by
    rw [← Spec.map_comp]
    rfl
  refine IsPullback.of_right ?_ (by rw [geometricFiberToFiniteLevel_comp_finiteLevelToSpec]; rfl)
    (f.isPullback_finiteLevel K.1)
  rw [geometricFiberToFiniteLevel_comp_finiteLevelProj, e]
  exact f.isPullback_geometricFiber

/-- The square `X₀ ⊗_k K' ⟶ X₀ ⊗_k K ⟶ Spec K`, `X₀ ⊗_k K' ⟶ Spec K' ⟶ Spec K` is cartesian. -/
lemma isPullback_finiteLevelMap {K K' : FiniteIntermediateField k (AlgebraicClosure k)}
    (h : K ≤ K') :
    IsPullback (f.finiteLevelMap h) (f.finiteLevelToSpec K'.1) (f.finiteLevelToSpec K.1)
      (specMap h) := by
  refine IsPullback.of_right ?_ (by simp) (f.isPullback_finiteLevel K.1)
  rw [finiteLevelMap_comp_finiteLevelProj, ← Spec.map_comp]
  exact f.isPullback_finiteLevel K'.1

instance {K K' : (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ} (g : K ⟶ K') :
    IsAffineHom (f.finiteLevelDiagram.map g) :=
  MorphismProperty.of_isPullback (f.isPullback_finiteLevelMap (leOfHom g.unop)).flip
    (isAffineHom_of_isAffine _)

instance [CompactSpace X₀] (K : (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ) :
    CompactSpace (f.finiteLevelDiagram.obj K) :=
  QuasiCompact.compactSpace_of_compactSpace (f.finiteLevelProj K.unop.1)

instance [QuasiSeparatedSpace X₀] (K : (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ) :
    QuasiSeparatedSpace (f.finiteLevelDiagram.obj K) :=
  have : QuasiSeparated (f.finiteLevelProj K.unop.1) :=
    MorphismProperty.of_isPullback (f.isPullback_finiteLevel K.unop.1).flip inferInstance
  quasiSeparatedSpace_of_quasiSeparated (f.finiteLevelProj K.unop.1)

/-- The morphism `ι : X̄ ⟶ X₀ ⊗_k K` is surjective, as a base change of `Spec k̄ ⟶ Spec K`. -/
instance surjective_geometricFiberToFiniteLevel
    (K : FiniteIntermediateField k (AlgebraicClosure k)) :
    Surjective (f.geometricFiberToFiniteLevel K.1.val) := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K.1 (AlgebraicClosure k)))) :=
    ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact MorphismProperty.of_isPullback (f.isPullback_geometricFiberToFiniteLevel K).flip this

/-- **The geometric fibre is the limit of the finite levels**: `X₀ ⊗_k k̄ = lim_K X₀ ⊗_k K` over
the finite subextensions `K` of `k̄ / k`, since `Spec k̄ = lim_K Spec K`
(`AlgebraicGeometry.FiniteIntermediateField.isLimitSpecCone`) and base change commutes with
connected limits. -/
def isLimitFiniteLevelCone : IsLimit f.finiteLevelCone :=
  have : IsConnected (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ :=
    IsCofiltered.isConnected _
  isLimitOfIsPullbackOfIsConnected f.finiteLevelDiagramToSpec f.finiteLevelCone
    (specCone k (AlgebraicClosure k))
    { hom := f.geometricFiberToAlgebraicClosure
      w K := by
        simp
        rfl }
    (fun K ↦ f.isPullback_geometricFiberToFiniteLevel K.unop)
    (isLimitSpecCone k (AlgebraicClosure k))

/-- **Locally constant functions on the geometric fibre are defined at a finite level.** For a
quasi-compact quasi-separated `X₀` over a field `k`, every locally constant function `g` on
`X̄ = X₀ ⊗_k k̄` is `g' ∘ ι` for a locally constant function `g'` on a finite level `X₀ ⊗_k K`,
`ι = 𝟙 × Spec (K ↪ k̄)`. -/
theorem exists_isLocallyConstant_comp_geometricFiberToFiniteLevel [CompactSpace X₀]
    [QuasiSeparatedSpace X₀] {α : Type*} [Nonempty α] {g : f.geometricFiber → α}
    (hg : IsLocallyConstant g) :
    ∃ (K : FiniteIntermediateField k (AlgebraicClosure k)) (g' : f.finiteLevel K.1 → α),
      IsLocallyConstant g' ∧ g' ∘ f.geometricFiberToFiniteLevel K.1.val = g := by
  obtain ⟨K, g', hg', h⟩ :=
    exists_isLocallyConstant_comp_eq_of_isLimit _ _ f.isLimitFiniteLevelCone hg
  exact ⟨K.unop, g', hg', h⟩

/-- The geometric fibre of a scheme locally of finite type over `k` is locally noetherian, being
locally of finite type over the field `k̄`. -/
instance isLocallyNoetherian_geometricFiber [LocallyOfFiniteType f] :
    IsLocallyNoetherian f.geometricFiber :=
  have : LocallyOfFiniteType f.geometricFiberToAlgebraicClosure :=
    MorphismProperty.of_isPullback f.isPullback_geometricFiber ‹_›
  LocallyOfFiniteType.isLocallyNoetherian f.geometricFiberToAlgebraicClosure

section Adic

open PadicAlgCl

variable (l : ℕ) [Fact l.Prime]

/-- **Sections of the constant `ℓ`-adic sheaf over the geometric fibre are defined at a finite
level.** Let `X₀` be quasi-compact and quasi-separated over a field `k` with locally connected
geometric fibre `X̄` (e.g. `X₀` of finite type over `k`). Every section `s` of `ℚ̄_ℓ` over `X̄`,
i.e. every locally finite continuous function `X̄ → ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.adicConstantSheaf_obj_obj`), is the pullback `s' ∘ ι` of a section
`s'` over a finite level `X₀ ⊗_k K`: being continuous with values in the totally disconnected
`ℚ̄_ℓ`, `s` is locally constant, so it is defined at a finite level
(`AlgebraicGeometry.Scheme.Hom.exists_isLocallyConstant_comp_geometricFiberToFiniteLevel`). -/
theorem exists_locallyFiniteFunctionsComp_geometricFiberToFiniteLevel_eq [CompactSpace X₀]
    [QuasiSeparatedSpace X₀] [LocallyConnectedSpace f.geometricFiber]
    (s : locallyFiniteFunctions l f.geometricFiber) :
    ∃ (K : FiniteIntermediateField k (AlgebraicClosure k))
      (s' : locallyFiniteFunctions l (f.finiteLevel K.1)),
      locallyFiniteFunctionsComp l (f.geometricFiberToFiniteLevel K.1.val).base.hom s' = s := by
  obtain ⟨K, g', hg', h⟩ := f.exists_isLocallyConstant_comp_geometricFiberToFiniteLevel
    (s.1.continuous.isLocallyConstant)
  have : CompactSpace (f.finiteLevel K.1) :=
    QuasiCompact.compactSpace_of_compactSpace (f.finiteLevelProj K.1)
  refine ⟨K, ⟨⟨g', hg'.continuous⟩, mem_locallyFiniteFunctions_of_finiteDimensional
    (FiniteDimensional.span_of_finite _ hg'.range_finite)⟩,
    Subtype.ext (ContinuousMap.ext fun x ↦ congrFun h x)⟩

/-- A section of `ℚ̄_ℓ` over a finite level is determined by its pullback to the geometric fibre,
`ι : X̄ ⟶ X₀ ⊗_k K` being surjective. -/
lemma locallyFiniteFunctionsComp_geometricFiberToFiniteLevel_injective
    (K : FiniteIntermediateField k (AlgebraicClosure k)) :
    Function.Injective
      (locallyFiniteFunctionsComp l (f.geometricFiberToFiniteLevel K.1.val).base.hom) :=
  locallyFiniteFunctionsComp_injective _ (f.geometricFiberToFiniteLevel K.1.val).surjective

/-- **The sections of `ℚ̄_ℓ` over the geometric fibre are the filtered colimit of the sections
over the finite levels**: `Γ(X̄, ℚ̄_ℓ) = colim_K Γ(X₀ ⊗_k K, ℚ̄_ℓ)`, for `X₀` quasi-compact and
quasi-separated over `k` with locally connected geometric fibre (e.g. `X₀` of finite type over
`k`). Here `Γ(V, ℚ̄_ℓ)` is the module of locally finite continuous functions `V → ℚ̄_ℓ`
(`AlgebraicGeometry.adicFunctionsPresheaf`), the sections of the constant `ℓ`-adic sheaf over
any `V` weakly étale over `X₀` (`AlgebraicGeometry.ProEtale.adicConstantSheaf_obj_obj`). -/
def isColimitAdicFunctionsPresheafMapCoconeFiniteLevelCone [CompactSpace X₀]
    [QuasiSeparatedSpace X₀] [LocallyConnectedSpace f.geometricFiber] :
    IsColimit ((adicFunctionsPresheaf l ⋙ CategoryTheory.forget (WeilCoefficients.{u} l)).mapCocone
      f.finiteLevelCone.op) := by
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun i x y h ↦ ?_)
  · obtain ⟨K, s', hs'⟩ :=
      f.exists_locallyFiniteFunctionsComp_geometricFiberToFiniteLevel_eq l x.down
    exact ⟨Opposite.op (Opposite.op K), ULift.up s', ULift.ext hs'.symm⟩
  · refine ⟨i, 𝟙 i, ?_⟩
    have := f.locallyFiniteFunctionsComp_geometricFiberToFiniteLevel_injective l i.unop.unop
      (congrArg ULift.down h)
    obtain rfl : x = y := ULift.ext this
    rfl

end Adic

end Scheme.Hom

namespace Scheme.Hom

section Frobenius

open PadicAlgCl

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  (l : ℕ) [Fact l.Prime]

/-- **Frobenius-invariant sections of `ℚ̄_ℓ` over the geometric fibre come from `X₀`**:
`H⁰(X̄, ℚ̄_ℓ)^{Fr} = H⁰(X₀, ℚ̄_ℓ)`. Let `X₀` be quasi-compact and quasi-separated over the finite
field `k` with locally connected geometric fibre (e.g. `X₀` of finite type over `k`). A section
`s` of `ℚ̄_ℓ` over `X̄` invariant under the geometric Galois Frobenius `Fr` is the pullback
`t ∘ p` of a section `t` over `X₀`.

The proof: `s = s' ∘ ι` for a section `s'` at a finite level `X₀ ⊗_k K`
(`AlgebraicGeometry.Scheme.Hom.exists_locallyFiniteFunctionsComp_geometricFiberToFiniteLevel_eq`);
since `ι` is surjective and `Fr ≫ ι = ι ≫ Fr_K`, `s'` is invariant under `Fr_K` and its powers;
these form a Galois action on `X₀ ⊗_k K ⟶ X₀`
(`AlgebraicGeometry.ProEtale.isGaloisAction_finiteLevelFrobeniusPow`), so `s'` and hence `s` are
constant on the fibres of the projections to `X₀`, and `s` descends along the quotient map
`p : X̄ ⟶ X₀` (flat, quasi-compact and surjective). -/
theorem exists_locallyFiniteFunctionsComp_geometricFiberProj_eq [CompactSpace X₀]
    [QuasiSeparatedSpace X₀] [LocallyConnectedSpace f.geometricFiber]
    (s : locallyFiniteFunctions l f.geometricFiber)
    (hs : locallyFiniteFunctionsComp l f.geometricGaloisFrobenius.asIso.hom.base.hom s = s) :
    ∃ t : locallyFiniteFunctions l X₀,
      locallyFiniteFunctionsComp l f.geometricFiberProj.base.hom t = s := by
  have := Fintype.ofFinite k
  obtain ⟨K, s', hs'⟩ := f.exists_locallyFiniteFunctionsComp_geometricFiberToFiniteLevel_eq l s
  have := K.2
  have hsx (x : f.geometricFiber) : s.1 x = s'.1 (f.geometricFiberToFiniteLevel K.1.val x) := by
    rw [← hs']
    rfl
  have hFr (x : f.geometricFiber) : s.1 (f.geometricGaloisFrobenius.asIso.hom x) = s.1 x := by
    conv_rhs => rw [← hs]
    rfl
  have h₁ (y : f.finiteLevel K.1) : s'.1 (f.finiteLevelFrobenius K.1 y) = s'.1 y := by
    obtain ⟨x, rfl⟩ := (f.geometricFiberToFiniteLevel K.1.val).surjective y
    rw [← Scheme.Hom.comp_apply, ← geometricGaloisFrobenius_hom_comp_geometricFiberToFiniteLevel,
      Scheme.Hom.comp_apply, ← hsx, ← hsx, hFr]
  have h₂ (m : ℕ) (y : f.finiteLevel K.1) :
      s'.1 (f.finiteLevelFrobeniusPow K.1 m y) = s'.1 y := by
    induction m generalizing y with
    | zero => rw [finiteLevelFrobeniusPow_zero, h₁]
    | succ m ih => rw [finiteLevelFrobeniusPow_succ, Scheme.Hom.comp_apply, ih, h₁]
  have h₃ (y₁ y₂ : f.finiteLevel K.1)
      (h : f.finiteLevelProj K.1 y₁ = f.finiteLevelProj K.1 y₂) : s'.1 y₁ = s'.1 y₂ := by
    obtain ⟨U, hU, hUρ⟩ := ProEtale.isGaloisAction_finiteLevelFrobeniusPow f K.1 _
      (pullback.fst (f.finiteLevelProj K.1) (f.finiteLevelProj K.1)) (pullback.snd _ _)
      pullback.condition
    obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback y₁ y₂ h
    obtain ⟨i, hi⟩ := hU z
    have := congrArg (fun φ : ↑(U i) ⟶ f.finiteLevel K.1 ↦ φ ⟨z, hi⟩) (hUρ i)
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at this
    rw [this, h₂]
  have h₄ : Function.FactorsThrough s.1 f.geometricFiberProj := fun x₁ x₂ h ↦ by
    rw [hsx, hsx]
    refine h₃ _ _ ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      geometricFiberToFiniteLevel_comp_finiteLevelProj]
    exact h
  have hp : Topology.IsQuotientMap f.geometricFiberProj := Flat.isQuotientMap_of_surjective _
  have : CompactSpace f.geometricFiber :=
    QuasiCompact.compactSpace_of_compactSpace f.geometricFiberProj
  have := finiteDimensional_span_range_of_mem_locallyFiniteFunctions s.2
  refine ⟨⟨hp.lift s.1 h₄, mem_locallyFiniteFunctions_of_finiteDimensional ?_⟩,
    Subtype.ext (hp.lift_comp s.1 h₄)⟩
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l] (Set.range s.1))
    (Submodule.span_mono ?_)
  rintro _ ⟨x₀, rfl⟩
  obtain ⟨x, rfl⟩ := f.geometricFiberProj.surjective x₀
  exact ⟨x, (ContinuousMap.congr_fun (hp.lift_comp s.1 h₄) x).symm⟩

omit [Finite k] in
/-- A section of `ℚ̄_ℓ` over `X₀` is determined by its pullback to the geometric fibre,
`p : X̄ ⟶ X₀` being surjective. -/
lemma locallyFiniteFunctionsComp_geometricFiberProj_injective :
    Function.Injective (locallyFiniteFunctionsComp l f.geometricFiberProj.base.hom) :=
  locallyFiniteFunctionsComp_injective _ f.geometricFiberProj.surjective

end Frobenius

section ProEt

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The diagram `K ↦ (X₀ ⊗_k K ⟶ X₀)` of the finite levels, in the pro-étale site of `X₀`. -/
@[simps]
def finiteLevelProEtDiagram :
    (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ ⥤ X₀.ProEt where
  obj K := Scheme.ProEt.mk (f.finiteLevelProj K.unop.1)
  map g := MorphismProperty.Over.homMk (f.finiteLevelMap (leOfHom g.unop))
  map_id K := MorphismProperty.Over.Hom.ext (f.finiteLevelDiagram.map_id K)
  map_comp g g' := MorphismProperty.Over.Hom.ext (f.finiteLevelDiagram.map_comp g g')

/-- The geometric fibre `X̄ ⟶ X₀`, as a cone over the finite levels in the pro-étale site of
`X₀`. -/
def finiteLevelProEtCone : Cone f.finiteLevelProEtDiagram where
  pt := Scheme.ProEt.mk f.geometricFiberProj
  π := { app K := MorphismProperty.Over.homMk (f.geometricFiberToFiniteLevel K.unop.1.val)
          (f.geometricFiberToFiniteLevel_comp_finiteLevelProj _)
         naturality _ _ g := MorphismProperty.Over.Hom.ext (f.finiteLevelCone.π.naturality g) }

variable (l : ℕ) [Fact l.Prime]

/-- **The sections of the condensed coefficient ring over the geometric fibre are the colimit of
the sections over the finite levels**: for the condensed model `Λ_X₀ = p_X₀^* ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.condensedRingObj`) and the objects `X̄ ⟶ X₀` and
`X₀ ⊗_k K ⟶ X₀` of the pro-étale site of `X₀`, `Λ_X₀(X̄) = colim_K Λ_X₀(X₀ ⊗_k K)`, for `X₀`
quasi-compact and quasi-separated over the finite field `k` with locally connected geometric
fibre (e.g. `X₀` of finite type over `k`). This is
`AlgebraicGeometry.Scheme.Hom.isColimitAdicFunctionsPresheafMapCoconeFiniteLevelCone`
transported along `Λ_X₀ ≅ ℚ̄_ℓ,X₀` (`AlgebraicGeometry.ProEtale.condensedRingObjIsoForgetAb`). -/
def isColimitCondensedRingObjMapCoconeFiniteLevelProEtCone [CompactSpace X₀]
    [QuasiSeparatedSpace X₀] [LocallyConnectedSpace f.geometricFiber] :
    IsColimit (((ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X₀).obj ⋙
      CategoryTheory.forget Ab.{u + 1}).mapCocone f.finiteLevelProEtCone.op) := by
  have h : IsColimit (((ProEtale.adicConstantSheaf l X₀).obj ⋙
      CategoryTheory.forget (WeilCoefficients.{u} l)).mapCocone f.finiteLevelProEtCone.op) := by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun i x y h ↦ ?_)
    · obtain ⟨K, s', hs'⟩ :=
        f.exists_locallyFiniteFunctionsComp_geometricFiberToFiniteLevel_eq l x.down
      exact ⟨Opposite.op (Opposite.op K), ULift.up s', ULift.ext hs'.symm⟩
    · refine ⟨i, 𝟙 i, ?_⟩
      obtain rfl : x = y := ULift.ext
        (f.locallyFiniteFunctionsComp_geometricFiberToFiniteLevel_injective l i.unop.unop
          (congrArg ULift.down h))
      rfl
  refine IsColimit.mapCoconeEquiv ?_ h
  exact Functor.isoWhiskerLeft _ (eqToIso HasForget₂.forget_comp).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((sheafToPresheaf _ _).mapIso
      (ProEtale.condensedRingObjIsoForgetAb l X₀)).symm _


/-- The projection `p : X̄ ⟶ X₀`, as a morphism to the terminal object of the pro-étale site of
`X₀`. -/
def geometricFiberProjProEt : Scheme.ProEt.mk f.geometricFiberProj ⟶ Scheme.ProEt.mk (𝟙 X₀) :=
  MorphismProperty.Over.homMk f.geometricFiberProj (Category.comp_id _)

/-- The geometric Galois Frobenius `Fr` of `X̄`, as an endomorphism of the object `X̄ ⟶ X₀` of
the pro-étale site of `X₀`. -/
def geometricGaloisFrobeniusProEt :
    Scheme.ProEt.mk f.geometricFiberProj ⟶ Scheme.ProEt.mk f.geometricFiberProj :=
  MorphismProperty.Over.homMk f.geometricGaloisFrobenius.asIso.hom
    (f.geometricGaloisFrobenius_hom_comp_geometricFiberProj)

/-- **Frobenius-invariant sections of the condensed coefficient ring over the geometric fibre
come from `X₀`**: `Λ_X₀(X̄)^{Fr} = Λ_X₀(X₀)` for the condensed model `Λ_X₀ = p_X₀^* ℚ̄_ℓ`, for
`X₀` quasi-compact and quasi-separated over the finite field `k` with locally connected
geometric fibre (e.g. `X₀` of finite type over `k`). This is
`AlgebraicGeometry.Scheme.Hom.exists_locallyFiniteFunctionsComp_geometricFiberProj_eq`
transported along `Λ_X₀ ≅ ℚ̄_ℓ,X₀` (`AlgebraicGeometry.ProEtale.condensedRingObjIsoForgetAb`). -/
theorem exists_condensedRingObj_map_geometricFiberProjProEt_eq [CompactSpace X₀]
    [QuasiSeparatedSpace X₀] [LocallyConnectedSpace f.geometricFiber]
    (x : (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X₀).obj.obj
      (Opposite.op (Scheme.ProEt.mk f.geometricFiberProj)))
    (hx : (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X₀).obj.map
      f.geometricGaloisFrobeniusProEt.op x = x) :
    ∃ y : (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X₀).obj.obj
        (Opposite.op (Scheme.ProEt.mk (𝟙 X₀))),
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X₀).obj.map
        f.geometricFiberProjProEt.op y = x := by
  let e := (sheafToPresheaf _ _).mapIso (ProEtale.condensedRingObjIsoForgetAb l X₀)
  let G := (ProEtale.weilCoefficientsForgetAb l X₀).obj (ProEtale.adicConstantSheaf l X₀)
  let P := Opposite.op (Scheme.ProEt.mk f.geometricFiberProj)
  have h₁ : G.obj.map f.geometricGaloisFrobeniusProEt.op (e.hom.app P x) = e.hom.app P x := by
    have := ConcreteCategory.congr_hom (e.hom.naturality f.geometricGaloisFrobeniusProEt.op) x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    exact this.symm.trans (congrArg (e.hom.app P) hx)
  obtain ⟨t, ht⟩ := f.exists_locallyFiniteFunctionsComp_geometricFiberProj_eq l
    (e.hom.app P x).down (congrArg ULift.down h₁)
  refine ⟨e.inv.app (Opposite.op (Scheme.ProEt.mk (𝟙 X₀))) (ULift.up t), ?_⟩
  have h₂ := ConcreteCategory.congr_hom (e.inv.naturality f.geometricFiberProjProEt.op)
    (ULift.up t)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₂
  refine h₂.symm.trans ?_
  have h₃ : G.obj.map f.geometricFiberProjProEt.op (ULift.up t) = e.hom.app P x :=
    ULift.ext ht
  have h₄ := ConcreteCategory.congr_hom (e.hom_inv_id_app P) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h₄
  exact (congrArg (e.inv.app P) h₃).trans h₄
end ProEt

end Scheme.Hom

namespace ProEtale.AdicSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

open PadicAlgCl

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  {l : ℕ} [Fact l.Prime] {ι κ : Type} [Fintype ι] [Fintype κ]

omit [Finite k] in
/-- Pullback of morphisms between finite free `ℓ`-adic sheaves along a surjective weakly étale
morphism is injective, by the matrix description
`AlgebraicGeometry.ProEtale.AdicSheaf.unitMatrix_adicUpperStar`. -/
lemma freeUpperStarIso_conj_injective {V W : Scheme.{u}} (g : W ⟶ V) [WeaklyEtale g]
    [Surjective g] :
    Function.Injective fun ψ₀ : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V ↦
      (freeUpperStarIso l ι g).inv ≫ (g)^*ᵃ[l].map ψ₀ ≫ (freeUpperStarIso l κ g).hom := by
  intro ψ₁ ψ₂ h
  have h' := congrArg unitMatrix h
  simp only [unitMatrix_adicUpperStar] at h'
  exact unitMatrix_injective (Matrix.ext fun i j ↦
    locallyFiniteFunctionsComp_injective _ g.surjective (congrFun (congrFun h' i) j))

/-- **Descent of Frobenius-invariant morphisms between constant finite free `ℓ`-adic sheaves on
the geometric fibre.** Let `X₀` be quasi-compact and quasi-separated over the finite field `k`
with locally connected geometric fibre (e.g. `X₀` of finite type over `k`). A morphism
`ψ : ℚ̄_ℓ,X̄^ι ⟶ ℚ̄_ℓ,X̄^κ` commuting with the geometric Galois Frobenius `Fr`, i.e. with the
canonical trivialisations `Fr^* ℚ̄_ℓ,X̄^ι ≅ ℚ̄_ℓ,X̄^ι`, is the pullback `p^* ψ₀` (along
`p : X̄ ⟶ X₀`, up to the canonical trivialisations) of a morphism
`ψ₀ : ℚ̄_ℓ,X₀^ι ⟶ ℚ̄_ℓ,X₀^κ`. The entries of the matrix of `ψ` are `Fr`-invariant sections of
`ℚ̄_ℓ` over `X̄` (`AlgebraicGeometry.ProEtale.AdicSheaf.unitMatrix_adicUpperStar`), so they descend
to `X₀` (`AlgebraicGeometry.Scheme.Hom.exists_locallyFiniteFunctionsComp_geometricFiberProj_eq`).
-/
theorem exists_freeUpperStarIso_geometricFiberProj_eq [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    [LocallyConnectedSpace f.geometricFiber]
    (ψ : (⨁ fun _ : ι ↦ unit l f.geometricFiber) ⟶ ⨁ fun _ : κ ↦ unit l f.geometricFiber)
    (hψ : (freeUpperStarIso l ι f.geometricGaloisFrobenius.asIso.hom).inv ≫
        (f.geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map ψ ≫
          (freeUpperStarIso l κ f.geometricGaloisFrobenius.asIso.hom).hom = ψ) :
    ∃ ψ₀ : (⨁ fun _ : ι ↦ unit l X₀) ⟶ ⨁ fun _ : κ ↦ unit l X₀,
      (freeUpperStarIso l ι f.geometricFiberProj).inv ≫ (f.geometricFiberProj)^*ᵃ[l].map ψ₀ ≫
        (freeUpperStarIso l κ f.geometricFiberProj).hom = ψ := by
  have hN := unitMatrix_adicUpperStar f.geometricGaloisFrobenius.asIso.hom ψ
  rw [hψ] at hN
  have h (i : κ) (j : ι) : ∃ t : locallyFiniteFunctions l X₀,
      locallyFiniteFunctionsComp l f.geometricFiberProj.base.hom t = unitMatrix ψ i j :=
    f.exists_locallyFiniteFunctionsComp_geometricFiberProj_eq l _
      (congrFun (congrFun hN i) j).symm
  choose t ht using h
  refine ⟨ofUnitMatrix (Matrix.of t), unitMatrix_injective ?_⟩
  rw [unitMatrix_adicUpperStar, unitMatrix_ofUnitMatrix]
  exact Matrix.ext fun i j ↦ ht i j

end ProEtale.AdicSheaf

end AlgebraicGeometry
