/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLisseOpen
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# The derived tensor product of bounded constructible complexes

Let `Λ` be a commutative condensed ring such that, on every scheme with noetherian underlying
space, the pro-étale locally finitely presented module objects over `Λ` are locally free and the
bounded constructible complexes form a triangulated subcategory. This holds for the field
coefficients `E̲` (`E` a finite extension of `ℚ_ℓ`) and `ℚ̲̄_ℓ`, whose locally finitely presented
module objects are the lisse sheaves of Bhatt–Scholze, Definition 6.8.6
(`ProEtale.CondensedRing.tensorHypotheses_padicAlgClRingObj`,
`ProEtale.CondensedRing.tensorHypotheses_continuousMapRingObj`). Then the bounded constructible
complexes on a scheme `T` with noetherian underlying space are stable under the derived tensor
product
(`ProEtale.CondensedRing.boundedConstructible_tensorObj`, blueprint
`proposition-six-operations-dctf--14` for the field coefficients).

## The argument

* If `A` is bounded with locally free cohomology sheaves and `L` is bounded constructible, then
  `A ⊗ᴸ L` is bounded constructible
  (`ProEtale.CondensedRing.boundedConstructible_tensorObj_of_isLocallyFree_homology`): by
  dévissage in both variables it suffices to treat `P[0] ⊗ᴸ N[0] ≅ (P ⊗ N)[0]` for `P` locally
  free and `N` constructible, and `P ⊗ N` is constructible.
* In general, argue by noetherian induction on the closed subset of `T` supporting a closed
  subscheme `D`. On a nonempty open `V` of `D` and after a surjective closed immersion
  `c : E ⟶ V`, the cohomology sheaves of both `K` and `L` are lisse
  (`ProEtale.CondensedRing.exists_isLocallyFinitelyPresented_homology_upperStar₂`), so
  `Lc^* (K ⊗ᴸ L) ≅ Lc^* K ⊗ᴸ Lc^* L` is bounded constructible on `E` by the field `tensorObj` of
  `ProEtale.CondensedRing.LisseTensorHypotheses` (when lisse sheaves are locally free, this
  follows from the previous point, a bounded complex with lisse cohomology sheaves being bounded
  constructible:
  `ProEtale.CondensedRing.boundedConstructible_of_isLocallyFinitelyPresented_homology`), and so is
  its pushforward `Rc_* Lc^* (K ⊗ᴸ L) ≅ K ⊗ᴸ L|_V` (the closed complement of `c` being empty). On
  the closed complement of `V`, `K ⊗ᴸ L` restricts to the tensor product of the restrictions,
  which is bounded constructible by induction. Bounded constructibility is local for an
  open–closed decomposition (`ProEtale.CondensedRing.boundedConstructible_of_openClosed`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that the
latter can use these statements.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- The tensor product `P[0] ⊗ᴸ L` of a locally free module object `P` placed in degree `0` and
a bounded constructible complex `L` is bounded constructible: by dévissage in `L`, this reduces
to `P[0] ⊗ᴸ N[0] ≅ (P ⊗ N)[0]` with `N` constructible. -/
lemma boundedConstructible_singleFunctor_tensorObj_of_isLocallyFree {Z : Scheme.{u}}
    [(boundedConstructible (condensedRingObj Λ Z)).IsTriangulated]
    {P : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)}
    (hP : IsLocallyFree (condensedRingObj Λ Z) P)
    {L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))}
    (hL : boundedConstructible (condensedRingObj Λ Z) L) :
    boundedConstructible (condensedRingObj Λ Z) ((DerivedCategory.singleFunctor _ 0).obj P ⊗ L) :=
  boundedConstructible_obj_of_forall_singleFunctor
    ((curriedTensor _).obj ((DerivedCategory.singleFunctor _ 0).obj P)) (fun N hN ↦
      (boundedConstructible _).prop_of_iso (hP.singleFunctorTensorObjIso N 0).symm
        (boundedConstructible_singleFunctor_zero_obj Λ _
          (hP.isConstructibleModuleObject_tensorObj hN))) hL

/-- The tensor product `A ⊗ᴸ L` of a bounded complex `A` with locally free cohomology sheaves and
a bounded constructible complex `L` is bounded constructible: by dévissage in `A`, this reduces
to `P[0] ⊗ᴸ L` with `P` locally free
(`ProEtale.CondensedRing.boundedConstructible_singleFunctor_tensorObj_of_isLocallyFree`). -/
lemma boundedConstructible_tensorObj_of_isLocallyFree_homology {Z : Scheme.{u}}
    [(boundedConstructible (condensedRingObj Λ Z)).IsTriangulated]
    {A L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))}
    (hA : DerivedCategory.TStructure.t.bounded A)
    (hA' : ∀ n, IsLocallyFree (condensedRingObj Λ Z) ((DerivedCategory.homologyFunctor _ n).obj A))
    (hL : boundedConstructible (condensedRingObj Λ Z) L) :
    boundedConstructible (condensedRingObj Λ Z) (A ⊗ L) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsLocallyFree (condensedRingObj Λ Z)) :=
    ⟨fun e h ↦ h.of_iso e⟩
  exact DerivedCategory.prop_of_bounded
    ((boundedConstructible (condensedRingObj Λ Z)).inverseImage ((curriedTensor _).flip.obj L))
    (IsLocallyFree (condensedRingObj Λ Z))
    (fun _ hP ↦ boundedConstructible_singleFunctor_tensorObj_of_isLocallyFree hP hL) A hA hA'

variable (Λ) in
/-- The hypotheses on the coefficient ring `Λ` under which the bounded constructible complexes
are stable under `⊗ᴸ`: on schemes with noetherian underlying space, the pro-étale locally finitely
presented module objects are locally free, and the bounded constructible complexes form a
triangulated subcategory. -/
structure TensorHypotheses : Prop where
  isLocallyFree (Z : Scheme.{u}) [TopologicalSpace.NoetherianSpace Z]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ Z) M → IsLocallyFree (condensedRingObj Λ Z) M
  isTriangulated (Z : Scheme.{u}) [TopologicalSpace.NoetherianSpace Z] :
    (boundedConstructible (condensedRingObj Λ Z)).IsTriangulated

variable (Λ) in
/-- The hypotheses on the coefficient ring `Λ` used by the noetherian induction proving that the
bounded constructible complexes are stable under `⊗ᴸ`: on schemes with noetherian underlying
space, the bounded constructible complexes form a triangulated subcategory, and `A ⊗ᴸ L` is
bounded constructible for `A` and `L` bounded with pro-étale locally finitely presented (lisse)
cohomology sheaves. -/
structure LisseTensorHypotheses : Prop where
  isTriangulated (Z : Scheme.{u}) [TopologicalSpace.NoetherianSpace Z] :
    (boundedConstructible (condensedRingObj Λ Z)).IsTriangulated
  tensorObj (Z : Scheme.{u}) [TopologicalSpace.NoetherianSpace Z]
    {A L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))}
    (hA : DerivedCategory.TStructure.t.bounded A)
    (hA' : ∀ n, IsLocallyFinitelyPresented (condensedRingObj Λ Z)
      ((DerivedCategory.homologyFunctor _ n).obj A))
    (hL : DerivedCategory.TStructure.t.bounded L)
    (hL' : ∀ n, IsLocallyFinitelyPresented (condensedRingObj Λ Z)
      ((DerivedCategory.homologyFunctor _ n).obj L)) :
    boundedConstructible (condensedRingObj Λ Z) (A ⊗ L)

variable (Λ) in
/-- A bounded complex whose cohomology sheaves are pro-étale locally finitely presented is bounded
constructible: a locally finitely presented module object is constructible for the trivial
stratification. -/
lemma boundedConstructible_of_isLocallyFinitelyPresented_homology {Z : Scheme.{u}}
    {L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))}
    (hL : DerivedCategory.TStructure.t.bounded L)
    (hL' : ∀ n, IsLocallyFinitelyPresented (condensedRingObj Λ Z)
      ((DerivedCategory.homologyFunctor _ n).obj L)) :
    boundedConstructible (condensedRingObj Λ Z) L :=
  ⟨hL, fun n ↦ ⟨Scheme.Stratification.trivial Z, fun _ ↦
    (isLocallyFinitelyPresented_mapMod_iff Λ _ _).2
      (IsLocallyFinitelyPresented.upperStar Λ (𝟙 Z) (hL' n))⟩⟩

/-- If the locally finitely presented module objects over `Λ` are locally free, the hypotheses
`ProEtale.CondensedRing.LisseTensorHypotheses` hold, by
`ProEtale.CondensedRing.boundedConstructible_tensorObj_of_isLocallyFree_homology` (a bounded
complex with lisse cohomology sheaves being bounded constructible). -/
theorem TensorHypotheses.lisseTensorHypotheses (hΛ : TensorHypotheses Λ) :
    LisseTensorHypotheses Λ where
  isTriangulated := hΛ.isTriangulated
  tensorObj Z _ _ _ hA hA' hL hL' :=
    have := hΛ.isTriangulated Z
    boundedConstructible_tensorObj_of_isLocallyFree_homology hA
      (fun n ↦ hΛ.isLocallyFree Z _ (hA' n))
      (boundedConstructible_of_isLocallyFinitelyPresented_homology Λ hL hL')

/-- The open piece of the induction step: if the cohomology sheaves of the pullbacks of the
bounded constructible complexes `K` and `L` to a surjective closed immersion `c : E ⟶ V` are
lisse, then `K ⊗ᴸ L` is bounded constructible on `V`. -/
lemma boundedConstructible_tensorObj_of_lisse (hΛ : LisseTensorHypotheses Λ) {V E : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace V] (c : E ⟶ V) [IsClosedImmersion c] [Surjective c]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V))}
    (hK : boundedConstructible (condensedRingObj Λ V) K)
    (hKc : ∀ n, IsLocallyFinitelyPresented (condensedRingObj Λ E)
      ((DerivedCategory.homologyFunctor _ n).obj ((L((c)^*⟦Λ⟧)).obj K)))
    (hL : boundedConstructible (condensedRingObj Λ V) L)
    (hLc : ∀ n, IsLocallyFinitelyPresented (condensedRingObj Λ E)
      ((DerivedCategory.homologyFunctor _ n).obj ((L((c)^*⟦Λ⟧)).obj L))) :
    boundedConstructible (condensedRingObj Λ V) (K ⊗ L) := by
  have : TopologicalSpace.NoetherianSpace E := c.isClosedEmbedding.isInducing.noetherianSpace
  have := hΛ.isTriangulated E
  -- the closed complement of `c` is empty, so the unit `K ⊗ L ⟶ Rc_* Lc^* (K ⊗ L)` is an iso
  have : IsEmpty (⊥ : V.Opens).toScheme := ⟨fun x ↦ by obtain ⟨x, hx⟩ := x; exact hx⟩
  have : QuasiCompact (⊥ : V.Opens).ι := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have hc : IsCompl (Set.range c.base) (Set.range (⊥ : V.Opens).ι.base) := by
    rw [Set.range_eq_univ.2 c.surjective, Scheme.Opens.range_ι]
    exact isCompl_top_bot
  have hu := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ
    (⊥ : V.Opens).ι c hc (K := K ⊗ L) (isZero_derivedCategory_of_isEmpty' Λ _)
  have hcK : boundedConstructible (condensedRingObj Λ E) ((L((c)^*⟦Λ⟧)).obj K) :=
    boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ c K hK
  have hcL : boundedConstructible (condensedRingObj Λ E) ((L((c)^*⟦Λ⟧)).obj L) :=
    boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ c L hL
  have hE : boundedConstructible (condensedRingObj Λ E) ((L((c)^*⟦Λ⟧)).obj (K ⊗ L)) :=
    (boundedConstructible _).prop_of_iso ((leftDerivedUpperStarTensorIso Λ c).app K |>.app L).symm
      (hΛ.tensorObj E hcK.1 hKc hcL.1 hLc)
  exact (boundedConstructible _).prop_of_iso
    (asIso ((derivedUpperStarLowerStarAdjunction Λ c).unit.app (K ⊗ L))).symm
    (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion Λ c hE)

/-- **The bounded constructible complexes are stable under the derived tensor product**, for a
coefficient ring `Λ` satisfying `ProEtale.CondensedRing.LisseTensorHypotheses`, on a scheme with
noetherian underlying space. -/
theorem boundedConstructible_tensorObj (hΛ : LisseTensorHypotheses Λ) {T : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace T]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))}
    (hK : boundedConstructible (condensedRingObj Λ T) K)
    (hL : boundedConstructible (condensedRingObj Λ T) L) :
    boundedConstructible (condensedRingObj Λ T) (K ⊗ L) := by
  suffices key : ∀ Z : TopologicalSpace.Closeds T, ∀ (D : Scheme.{u}) (c : D ⟶ T)
      [IsClosedImmersion c], Set.range c.base ⊆ Z →
      ∀ K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
        (condensedRingObj Λ D)), boundedConstructible _ K → boundedConstructible _ L →
        boundedConstructible (condensedRingObj Λ D) (K ⊗ L) from
    key ⊤ T (𝟙 T) (fun _ _ ↦ trivial) K L hK hL
  intro Z
  induction Z using WellFoundedLT.induction with
  | ind Z ih =>
  intro D c _ hcZ K L hK hL
  have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
  rcases isEmpty_or_nonempty D with hD | hD
  · exact boundedConstructible_of_isZero Λ (isZero_derivedCategory_of_isEmpty' Λ _)
  obtain ⟨V, E, c', ⟨v, hv⟩, _, _, hcK, hcL⟩ :=
    exists_isLocallyFinitelyPresented_homology_upperStar₂ hK hL
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hij : Set.range V.closedComplement.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]
  refine boundedConstructible_of_openClosed Λ V.ι V.closedComplement hij _ ?_ ?_
  · -- the open piece
    refine (boundedConstructible _).prop_of_iso
      ((leftDerivedUpperStarTensorIso Λ V.ι).app K |>.app L).symm ?_
    refine boundedConstructible_tensorObj_of_lisse hΛ c'
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ V.ι K hK) (fun n ↦ ?_)
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ V.ι L hL) (fun n ↦ ?_)
    · exact (hcK n).of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
        ((leftDerivedUpperStarComp Λ c' V.ι).app K))
    · exact (hcL n).of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
        ((leftDerivedUpperStarComp Λ c' V.ι).app L))
  · -- the closed piece, by induction
    let Z' : TopologicalSpace.Closeds T := ⟨c.base '' Set.range V.closedComplement.base,
      c.isClosedEmbedding.isClosedMap _ V.closedComplement.isClosedEmbedding.isClosed_range⟩
    have hZ' : Z' < Z := by
      refine IsConcreteLE.lt_iff_le_and_exists.2 ⟨fun x ⟨w, _, hw⟩ ↦ hcZ ⟨w, hw⟩,
        c.base v, hcZ ⟨v, rfl⟩, fun ⟨w, hw, hwv⟩ ↦ ?_⟩
      rw [c.isClosedEmbedding.injective hwv, hij] at hw
      exact hw ⟨⟨v, hv⟩, rfl⟩
    have hrange : Set.range (V.closedComplement ≫ c).base ⊆ Z' := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact subset_rfl
    exact (boundedConstructible _).prop_of_iso
      ((leftDerivedUpperStarTensorIso Λ V.closedComplement).app K |>.app L).symm
      (ih Z' hZ' _ (V.closedComplement ≫ c) hrange _ _
        (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ _ K hK)
        (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ _ L hL))

variable (Λ) in
/-- The unit `Λ_X` of the derived tensor product is bounded constructible: it is the free module
object of rank one, placed in degree `0`. -/
lemma boundedConstructible_tensorUnit (X : Scheme.{u}) :
    boundedConstructible (condensedRingObj Λ X)
      (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)))) :=
  (boundedConstructible _).prop_of_iso (DerivedCategory.singleFunctorObjUnitIso _)
    (boundedConstructible_singleFunctor_zero_obj Λ _
      (isLocallyFree_tensorUnit Λ X).isConstructibleModuleObject)

end AlgebraicGeometry.ProEtale.CondensedRing
