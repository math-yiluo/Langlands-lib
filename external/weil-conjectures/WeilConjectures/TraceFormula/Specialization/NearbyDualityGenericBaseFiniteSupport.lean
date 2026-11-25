/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBase

/-!

# Nearby duality over a generic base: the finite-support step

For a trait model `M` over the generic base (`NearbyCyclesModel.IsTraitModelOfGenericBase`), the
cone of the duality map `δ_{M,K}` (`NearbyCyclesModel.nearbyDualityMapOfGenericBase`) is supported
on finitely many closed points of the special fibre
(`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMapOfGenericBase`), provided that
`δ` becomes an isomorphism on the special fibre of the generic slice of every coordinate of the
restrictions of the total space to opens (the generic-slice step of blueprint
`lemma-nearby-duality-slice--1`, taken as a hypothesis). This is the generic-base version of
`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMap`. If the special fibre is
finite, the cone is supported on all of its points
(`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMapOfGenericBase_of_finite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

/-- Vanishing on the special fibre of a slice implies vanishing on the fibre of its special
coordinate over the slice point. -/
private lemma isZero_upperStar_pullback_fst_of_sliceSpecialMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {k' K : Type u} [Field k'] [Field K] [Algebra k' K]
    {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (x : K) (hM : M.IsTraitModelOver q g)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X'.left) Ab.{u + 1})
      (condensedRingObj Λ X'.left)))
    (hC : IsZero (L((sliceSpecialMap x hM hb)^*⟦Λ⟧).obj C)) :
    IsZero (L((pullback.fst (specialCoordinate hM b hb) (traitSlicePoint x))^*⟦Λ⟧).obj C) := by
  obtain ⟨l, hl⟩ := exists_comp_sliceSpecialMap x hM hb
  rw [← hl]
  exact (L((l)^*⟦Λ⟧).map_isZero hC).of_iso ((leftDerivedUpperStarComp Λ l _).app C)

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

-- the triangles of the duality map live on large derived categories
/-- **Finite support of the cone of the duality map over a generic base, from the generic
slices** (blueprint `proposition-nearby-cycles-commute-verdier-duality`, "Dimension induction"): if,
for every open `V` of the total space embedded in an affine space `𝔸(ι_V; S)` over `S` (an immersion
`c_V`), and every coordinate `b : 𝒳_V ⟶ 𝔸¹_S` of the restriction `M|_V`, the
duality map of `M|_V` becomes an isomorphism on the special fibre of the generic slice of `b`
(`hslice`, the generic-slice step of blueprint `lemma-nearby-duality-slice--1`), then the duality
map `δ_{M,K}` is an isomorphism away from finitely many closed points of the special fibre. -/
theorem exists_finset_isIso_upperStar_nearbyDualityMapOfGenericBase
    (D : NearbyDualizingDataOfGenericBase k' ℓ) (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hslice : ∀ (V : M.total.Opens) [QuasiCompact V.ι] {ιV : Type u} [Finite ιV]
      (cV : (M.restrictOpen V).total ⟶ 𝔸(ιV; trait k')) [IsImmersion cV]
      (_ : cV ≫ 𝔸(ιV; trait k') ↘ trait k' = V.ι ≫ q)
      {b : (M.restrictOpen V).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
      (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = V.ι ≫ q)
      (L : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧),
      IsIso (L((sliceSpecialMap (traitSliceCoord k')
        (h.restrictOpen V).isTraitModelOver hb)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          (nearbyDualityMapOfGenericBase ℓ D (h.restrictOpen V) L).hom))
    (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ (S : Finset X'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι (finsetComplOpens S hS))).map (nearbyDualityMapOfGenericBase ℓ D h K)) := by
  have : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  have : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  have : IsNoetherian X'.left := ⟨⟩
  have hM := h.isTraitModelOver
  have := hM.isTraitModel.isNoetherian_total
  have := hM.locallyOfFiniteType
  obtain ⟨m, hm⟩ := Scheme.Hom.exists_locallyEmbedsInAffineSpace q
  obtain ⟨C, g', δ', hT⟩ := distinguished_cocone_triangle
    (nearbyDualityMapOfGenericBase ℓ D h K).hom
  have hC := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    X'.left)).ext_of_isTriangulatedClosed₃ _ hT
    ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj
      (verdierDual ℓ K)).property
    (verdierDual ℓ ((boundedConstructibleNearbyCycles
      (h.preservesBoundedConstructible (ℓ := ℓ))).obj K)).property
  suffices H : ∃ (S : Finset X'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsZero (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) by
    obtain ⟨S, hS, hz⟩ := H
    refine ⟨S, hS, ?_⟩
    have hiso := (Triangle.isZero₃_iff_isIso₁ _
      (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _
        hT)).1 hz
    have : IsIso ((boundedConstructible _).ι.map ((boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι (finsetComplOpens S hS))).map
          (nearbyDualityMapOfGenericBase ℓ D h K))) := hiso
    exact isIso_of_fully_faithful (boundedConstructible _).ι _
  refine exists_finset_isZero_of_forall_exists_coordinates X' hC fun z ↦ ?_
  obtain ⟨V, hzV, ιV, _, cV, -, hcVi, hcV⟩ := hm (M.i z)
  have : QuasiCompact V.ι := inferInstance
  have hR := h.restrictOpen V
  have hRM := hR.isTraitModelOver
  let coord : ιV → ((M.restrictOpen V).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')) :=
    fun a ↦ cV ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')
  have hcoord : ∀ a, coord a ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = V.ι ≫ q :=
    fun a ↦ by simp [coord, hcV]
  refine ⟨M.i ⁻¹ᵁ V, hzV, ιV, inferInstance,
    fun a ↦ specialCoordinate hRM (coord a) (hcoord a), fun a ↦ ?_, fun v hv ↦ ?_, fun a ↦ ?_⟩
  · -- the coordinates are locally of finite type
    have h' := specialCoordinate_over hRM (coord a) (hcoord a)
    have : LocallyOfFiniteType (specialCoordinate hRM (coord a) (hcoord a) ≫
        𝔸(ULift.{u} (Fin 1); Spec (.of k')) ↘ Spec (.of k')) := by
      rw [h']
      infer_instance
    exact locallyOfFiniteType_of_comp _ (𝔸(ULift.{u} (Fin 1); Spec (.of k')) ↘ Spec (.of k'))
  · -- the coordinates detect closed points
    have := hcVi
    refine isClosed_singleton_of_isImmersion hRM cV hcV v fun a ↦ ?_
    have hva := hv a
    dsimp only at hva
    rwa [show specialCoordinate hRM (coord a) (hcoord a) =
        specialCoordinate hRM cV hcV ≫ AffineSpace.reindex (fun _ ↦ a) (Spec (.of k')) from
      specialCoordinate_comp_reindex hRM cV hcV _] at hva
  · -- the cone vanishes over the generic point of each coordinate line
    refine ⟨traitSliceField k', inferInstance, traitSlicePoint (traitSliceCoord k'),
      ⟨⊥, Ideal.isPrime_bot⟩, isGenericPoint_traitSlicePoint_traitSliceCoord k' _, ?_⟩
    have : IsOpenImmersion (M.restrictOpenHom V).total := inferInstanceAs (IsOpenImmersion V.ι)
    have := hcVi
    have hs := hslice V cV hcV (hcoord a)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X₁)).obj K)
    have hs' := (isIso_map_map_nearbyDualityMapOfGenericBase_iff_of_isOpenImmersion ℓ
      (j := 𝟙 X₁) (j' := M.restrictSpecialFibreι V) ((boundedConstructible _).ι ⋙
        L((sliceSpecialMap (traitSliceCoord k') hRM (hcoord a))^*⟦Profinite.padicAlgClRingObj ℓ⟧))
      D (M.restrictOpenHom V) h hR (isPullback_morphismRestrict M.j V).flip rfl rfl K).2 hs
    let r' : (M.restrictSpecialFibre V).left ⟶ X'.left := (M.i ⁻¹ᵁ V).ι
    have hT₁ := L((r')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _ hT
    have hT₂ := L((sliceSpecialMap (traitSliceCoord k') hRM (hcoord a))^*⟦
      Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _ hT₁
    have hz := Triangle.isZero₃_of_isIso₁ _ hT₂ hs'
    exact isZero_upperStar_pullback_fst_of_sliceSpecialMap (Profinite.padicAlgClRingObj ℓ)
      (traitSliceCoord k') hRM (hcoord a) _ hz

/-- **The base case of the finite-support step over a generic base** (blueprint
`proposition-nearby-cycles-commute-verdier-duality`, "This also supplies the base case `n = 0`"): if
the special fibre `X'` has finitely many points, the duality map is an isomorphism away from all of
them, which are closed (`X'` is a finite Jacobson space, hence discrete). -/
theorem exists_finset_isIso_upperStar_nearbyDualityMapOfGenericBase_of_finite
    (D : NearbyDualizingDataOfGenericBase k' ℓ) (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    [Finite X'.left] (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ (S : Finset X'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι (finsetComplOpens S hS))).map (nearbyDualityMapOfGenericBase ℓ D h K)) := by
  have : JacobsonSpace X'.left := LocallyOfFiniteType.jacobsonSpace X'.hom
  have : Fintype X'.left := Fintype.ofFinite _
  refine ⟨Finset.univ, fun x _ ↦ isClosed_discrete _, ?_⟩
  have : IsEmpty (opensOver (finsetComplOpens (Finset.univ : Finset X'.left)
      fun x _ ↦ isClosed_discrete _)).left :=
    ⟨fun x ↦ x.2 (Finset.mem_coe.2 (Finset.mem_univ _))⟩
  have hz (A : Dᵇc((opensOver (finsetComplOpens (Finset.univ : Finset X'.left)
      fun x _ ↦ isClosed_discrete _)).left)⟦Profinite.padicAlgClRingObj ℓ⟧) : IsZero A :=
    IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι A
      (isZero_derivedCategory_of_isEmpty' _ _)
  exact ⟨(hz _).to_ _, (hz _).eq_of_src _ _, (hz _).eq_of_src _ _⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
