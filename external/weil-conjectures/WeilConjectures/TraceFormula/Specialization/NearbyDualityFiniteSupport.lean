/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityOpen
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFiniteSupport
public import WeilConjectures.TraceFormula.Specialization.SliceSupport

/-!

# Nearby duality: the finite-support step

For a trait model `M` over the base, the cone of the duality map `δ_{M,K}` is supported on
finitely many closed points of the special fibre
(`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMap`), provided that `δ` becomes an
isomorphism on the special fibre of the generic slice of every coordinate of the restrictions of
the total space to opens (the generic-slice step of blueprint `lemma-nearby-duality-slice--1`, taken
as a hypothesis): around every point of the special fibre, the coordinates of a local chart of the
total space detect closed points, and the cone vanishes over the generic point of each coordinate
line (`ProEtale.CondensedRing.exists_finset_isZero_of_forall_exists_coordinates`).

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

/-- Vanishing after pullback is preserved by any further factorization of the map. -/
private lemma isZero_leftDerivedUpperStar_of_factorization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y Z W : Scheme.{u}} (p : W ⟶ Y) (q : Z ⟶ Y)
    (hp : ∃ l : W ⟶ Z, l ≫ q = p)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) (hC : IsZero (L((q)^*⟦Λ⟧).obj C)) :
    IsZero (L((p)^*⟦Λ⟧).obj C) := by
  obtain ⟨l, hl⟩ := hp
  exact (L((l)^*⟦Λ⟧).map_isZero hC).of_iso ((leftDerivedUpperStarCompOfEq Λ hl).app C)

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

section Restrict

instance [LocallyOfFiniteType X'.hom] (V : M.total.Opens) :
    LocallyOfFiniteType (M.restrictSpecialFibre V).hom :=
  inferInstanceAs (LocallyOfFiniteType ((M.i ⁻¹ᵁ V).ι ≫ X'.hom))

instance [IsSeparated X'.hom] (V : M.total.Opens) :
    IsSeparated (M.restrictSpecialFibre V).hom :=
  inferInstanceAs (IsSeparated ((M.i ⁻¹ᵁ V).ι ≫ X'.hom))

instance [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] (V : M.total.Opens) :
    QuasiCompact (M.restrictSpecialFibre V).hom := by
  have : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  have : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  have : IsNoetherian X'.left := ⟨⟩
  exact inferInstanceAs (QuasiCompact ((M.i ⁻¹ᵁ V).ι ≫ X'.hom))

/-- The open immersion `i⁻¹ V ⟶ X'` of special fibres of the restriction of a model to an open
`V` of its total space, as a morphism of `k'`-schemes. -/
noncomputable def restrictSpecialFibreι (V : M.total.Opens) : M.restrictSpecialFibre V ⟶ X' :=
  Over.homMk (M.i ⁻¹ᵁ V).ι rfl

instance (V : M.total.Opens) : IsOpenImmersion (M.restrictSpecialFibreι V).left :=
  inferInstanceAs (IsOpenImmersion (M.i ⁻¹ᵁ V).ι)

/-- The restriction of a trait model over the base to an open `V` of its total space with
quasi-compact inclusion is a trait model over the base. -/
lemma IsTraitModelOfBase.restrictOpen (h : M.IsTraitModelOfBase k q g) (V : M.total.Opens)
    [QuasiCompact V.ι] :
    (M.restrictOpen V).IsTraitModelOfBase (X' := M.restrictSpecialFibre V) k (V.ι ≫ q)
      ((M.j ⁻¹ᵁ V).ι ≫ g) := by
  obtain ⟨e, he, he'⟩ := h.exists_comp_ε
  obtain ⟨u, _, hu₁, hu₂⟩ := h.exists_openImmersion
  refine ⟨h.isTraitModelOver.restrictOpen V, ⟨V.ι ≫ e, ?_, ?_⟩, (M.j ⁻¹ᵁ V).ι ≫ u,
    inferInstance, ?_, ?_⟩
  · change (M.j ∣_ V) ≫ V.ι ≫ e = (M.j ⁻¹ᵁ V).ι ≫ M.ε
    rw [morphismRestrict_ι_assoc, he]
  · change V.ι ≫ e ≫ X.hom = (V.ι ≫ q) ≫ traitToBase k k'
    rw [he', Category.assoc]
  · rw [Category.assoc, hu₁]
    rfl
  · rw [Category.assoc, hu₂]

end Restrict

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

section OpenRestriction

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {j : Y ⟶ X} {j' : Y' ⟶ X'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **Nearby duality and open restriction, after a further functor**: for an open sub-model
`φ : N ⟶ M` of trait models over the base and any functor `F` on the special fibre of `N`,
`F(j'^* δ_{M,K})` is invertible if and only if `F(δ_{N, j^* K})` is
(`NearbyCyclesModel.isIso_map_nearbyDualityMap_iff_of_isOpenImmersion` for `F = 𝟭`). -/
theorem isIso_map_map_nearbyDualityMap_iff_of_isOpenImmersion {E : Type*} [Category E]
    (F : Dᵇc(Y'.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ E) (D : NearbyDualizingData k k' ℓ)
    (φ : N.Hom M j.left j'.left) (hM : M.IsTraitModelOfBase k q g)
    (hN : N.IsTraitModelOfBase k qN gN) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : qN = φ.total ≫ q)
    (hg : gN = φ.generic ≫ g) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (F.map ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
        (nearbyDualityMap ℓ D hM K))) ↔
      IsIso (F.map (nearbyDualityMap ℓ D hN
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))) := by
  have e := nearbyDualityMap_restrict_boundedConstructible φ (hN.preservesBoundedConstructible ℓ)
    (hM.preservesBoundedConstructible ℓ) (D.θ hM)
    (D.θ hN) (dualizingComplexUpperStarIso ℓ j).hom
    (dualizingComplexUpperStarIso ℓ j').hom
    (D.map_θ_comp_dualizingComplexUpperStarIso hM hN j j' φ hφ hq hg)
    K
  have : IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    φ.isIso_pullbackExchange_of_isOpenImmersion _ hφ
  have : IsIso (φ.boundedConstructiblePullbackExchange ℓ (hN.preservesBoundedConstructible ℓ)
      (hM.preservesBoundedConstructible ℓ)) :=
    φ.isIso_boundedConstructiblePullbackExchange ℓ _ _
  have := isIso_nearbyDualityMap_upperStar_of_isOpenImmersion j' (dualizingComplexUpperStarIso ℓ j')
    ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible ℓ)).obj K)
  have := isIso_nearbyDualityMap_upperStar_of_isOpenImmersion j (dualizingComplexUpperStarIso ℓ j) K
  rw [← isIso_comp_right_iff _ (F.map (Verdier.nearbyDualityMap (Functor.LaxMonoidal.μ
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j'))
    (dualizingComplexUpperStarIso ℓ j').hom
    ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible ℓ)).obj K))),
    ← F.map_comp]
  unfold nearbyDualityMap
  rw [e]
  simp only [F.map_comp]
  rw [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]

end OpenRestriction

-- the triangles of the duality map live on large derived categories
/-- **Finite support of the cone of the duality map, from the generic slices** (blueprint
`proposition-nearby-cycles-commute-verdier-duality`, "Dimension induction"): if, for every open `V`
of the total space and every coordinate `b : 𝒳_V ⟶ 𝔸¹_S` of the restriction `M|_V`, the duality map
of `M|_V` becomes an isomorphism on the special fibre of the generic slice of `b` (`hslice`, the
generic-slice step of blueprint `lemma-nearby-duality-slice--1`), then the duality map `δ_{M,K}` is
an isomorphism away from finitely many closed points of the special fibre. -/
theorem exists_finset_isIso_upperStar_nearbyDualityMap (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g)
    (hslice : ∀ (V : M.total.Opens) [QuasiCompact V.ι]
      {b : (M.restrictOpen V).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
      (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = V.ι ≫ q)
      (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧),
      IsIso (L((sliceSpecialMap (traitSliceCoord k')
        (h.restrictOpen V).isTraitModelOver hb)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          (nearbyDualityMap ℓ D (h.restrictOpen V) L).hom))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ (S : Finset X'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι (finsetComplOpens S hS))).map (nearbyDualityMap ℓ D h K)) := by
  have : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  have : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  have : IsNoetherian X'.left := ⟨⟩
  have hM := h.isTraitModelOver
  have := hM.isTraitModel.isNoetherian_total
  have := hM.locallyOfFiniteType
  obtain ⟨m, hm⟩ := Scheme.Hom.exists_locallyEmbedsInAffineSpace q
  obtain ⟨C, g', δ', hT⟩ := distinguished_cocone_triangle (nearbyDualityMap ℓ D h K).hom
  have hC := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    X'.left)).ext_of_isTriangulatedClosed₃ _ hT
    ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj
      (verdierDual ℓ K)).property
    (verdierDual ℓ ((boundedConstructibleNearbyCycles
      (h.preservesBoundedConstructible ℓ)).obj K)).property
  suffices H : ∃ (S : Finset X'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsZero (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) by
    obtain ⟨S, hS, hz⟩ := H
    refine ⟨S, hS, ?_⟩
    have hiso := (Triangle.isZero₃_iff_isIso₁ _
      (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _
        hT)).1 hz
    have : IsIso ((boundedConstructible _).ι.map ((boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι (finsetComplOpens S hS))).map
          (nearbyDualityMap ℓ D h K))) := hiso
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
    have hs := hslice V (hcoord a)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)).obj K)
    have hs' := (isIso_map_map_nearbyDualityMap_iff_of_isOpenImmersion ℓ (j := 𝟙 X)
      (j' := M.restrictSpecialFibreι V) ((boundedConstructible _).ι ⋙
        L((sliceSpecialMap (traitSliceCoord k') hRM (hcoord a))^*⟦Profinite.padicAlgClRingObj ℓ⟧))
      D (M.restrictOpenHom V) h hR (isPullback_morphismRestrict M.j V).flip rfl rfl K).2 hs
    let r' : (M.restrictSpecialFibre V).left ⟶ X'.left := (M.i ⁻¹ᵁ V).ι
    have hT₁ := L((r')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _ hT
    have hT₂ := L((sliceSpecialMap (traitSliceCoord k') hRM (hcoord a))^*⟦
      Profinite.padicAlgClRingObj ℓ⟧).map_distinguished _ hT₁
    have hz : IsZero (L((sliceSpecialMap (traitSliceCoord k') hRM (hcoord a))^*⟦
        Profinite.padicAlgClRingObj ℓ⟧).obj (L((r')^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) :=
      Triangle.isZero₃_of_isIso₁ _ hT₂ hs'
    exact isZero_leftDerivedUpperStar_of_factorization (Profinite.padicAlgClRingObj ℓ) _ _
      (exists_comp_sliceSpecialMap (traitSliceCoord k') hRM (hcoord a)) _ hz

/-- **The base case of the finite-support step** (blueprint
`proposition-nearby-cycles-commute-verdier-duality`, "This also supplies the base case `n = 0`"): if
the special fibre `X'` has finitely many points, the duality map is an isomorphism away from all of
them, which are closed (`X'` is a finite Jacobson space, hence discrete). -/
theorem exists_finset_isIso_upperStar_nearbyDualityMap_of_finite
    (D : NearbyDualizingData k k' ℓ) (h : M.IsTraitModelOfBase k q g) [Finite X'.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ (S : Finset X'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι (finsetComplOpens S hS))).map (nearbyDualityMap ℓ D h K)) := by
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
