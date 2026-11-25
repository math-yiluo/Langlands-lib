/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomRightAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful

/-!
# The derived internal hom of bounded constructible complexes

Let `Λ` be a commutative condensed ring satisfying `ProEtale.CondensedRing.TensorHypotheses`
(locally finitely presented module objects are locally free and the bounded constructible
complexes form a triangulated subcategory, on schemes with noetherian underlying space): for
instance the field coefficients `E̲` and `ℚ̲̄_ℓ`. Let `T` be a scheme with noetherian underlying
space such that the derived pushforwards `Rj_*` along the open immersions `j` into closed
subschemes of `T` preserve bounded constructible complexes (Deligne's finiteness theorem, for `T`
of finite type over a field in which `ℓ` is invertible). Then the bounded constructible complexes
on `T` are stable under the derived internal hom `RHom(K, L)`
(`ProEtale.CondensedRing.boundedConstructible_ihom`, blueprint `proposition-six-operations-dctf--15`
for the field coefficients).

## The argument

* If `A` is bounded with locally free cohomology sheaves, then `RHom(A, L)` is bounded
  constructible for every bounded constructible `L`
  (`ProEtale.CondensedRing.boundedConstructible_ihom_of_isLocallyFree_homology`): by dévissage in
  `A` it suffices to treat `A = P[q]` with `P` locally free, which is dualizable with dual
  `P'[-q]`, so that `RHom(P[q], L) ≅ P'[-q] ⊗ᴸ L`.
* In general, argue by noetherian induction on the closed subset of `T` supporting a closed
  subscheme `D`. Let `V` be a nonempty open of `D` on which `K` is lisse after a surjective closed
  immersion `c : E ⟶ V`, `j : V ⟶ D` its inclusion and `i` the closed complement. Complete the
  unit `L ⟶ Rj_* Lj^* L` to a distinguished triangle `L ⟶ Rj_* Lj^* L ⟶ C ⟶ L[1]`; then
  `Lj^* C = 0`, so `C ≅ Ri_* Li^* C`. Applying `RHom(K, -)`, and using
  `RHom(K, Rf_* M) ≅ Rf_* RHom(Lf^* K, M)` (`ProEtale.CondensedRing.ihomRightDerivedLowerStarIso`),
  the second term is `Rj_* RHom(Lj^* K, Lj^* L)`, bounded constructible by the lisse case on `E`,
  and the third is `Ri_* RHom(Li^* K, Li^* C)`, bounded constructible by induction.

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that the
latter can use these statements.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

variable (Λ) in
/-- The internal form of the adjunction `Lf^* ⊣ Rf_*`:
`RHom(K, Rf_* M) ≅ Rf_* RHom(Lf^* K, M)`. -/
noncomputable def ihomRightDerivedLowerStarIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (ihom K).obj ((R((f)_*⟦Λ⟧)).obj M) ≅
      (R((f)_*⟦Λ⟧)).obj ((ihom ((L((f)^*⟦Λ⟧)).obj K)).obj M) :=
  ((derivedUpperStarLowerStarAdjunction Λ f).ihomCompIso K).app M

/-- The internal hom `RHom(A, L)` from a bounded complex `A` with locally free cohomology sheaves
to a bounded constructible complex `L` is bounded constructible: by dévissage in `A` this reduces
to `A = P[q]` with `P` locally free, and `RHom(P[q], L) ≅ P'[-q] ⊗ᴸ L` for the dual `P'[-q]` of
`P[q]`. -/
lemma boundedConstructible_ihom_of_isLocallyFree_homology (hΛ : TensorHypotheses Λ)
    {Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace Z]
    {A L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))}
    (hA : DerivedCategory.TStructure.t.bounded A)
    (hA' : ∀ n, IsLocallyFree (condensedRingObj Λ Z) ((DerivedCategory.homologyFunctor _ n).obj A))
    (hL : boundedConstructible (condensedRingObj Λ Z) L) :
    boundedConstructible (condensedRingObj Λ Z) ((ihom A).obj L) := by
  have := hΛ.isTriangulated Z
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsLocallyFree (condensedRingObj Λ Z)) :=
    ⟨fun e h ↦ h.of_iso e⟩
  let Q : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) := fun A ↦ boundedConstructible _ ((ihom A).obj L)
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ (boundedConstructible _).prop_of_iso
      ((MonoidalClosed.internalHom.mapIso e.op).app L).symm h⟩
  refine DerivedCategory.prop_of_bounded_of_degreewise Q (fun A hA ↦ ?_)
    (fun T hT h₁ h₃ ↦ ?_) (fun _ ↦ IsLocallyFree (condensedRingObj Λ Z)) (fun q P hP ↦ ?_) A hA hA'
  · refine boundedConstructible_of_isZero Λ ?_
    rw [IsZero.iff_id_eq_zero]
    apply ((ihom.adjunction A).homEquiv _ _).symm.injective
    exact (((curriedTensor _).flip.obj ((ihom A).obj L)).map_isZero hA).eq_of_src _ _
  · have := isLeftDerivabilityStructure_localizerMorphismKFlat Λ Z
    obtain ⟨h, hT'⟩ := DerivedCategory.exists_distinguished_ihom_pre T hT L
    exact (boundedConstructible _).ext_of_isTriangulatedClosed₂ _ hT' h₃ h₁
  · obtain ⟨P', hP', ⟨e⟩⟩ := hP.exists_exactPairing_singleFunctor q
    exact (boundedConstructible _).prop_of_iso (MonoidalClosed.ihomObjIsoTensor _ _ L).symm
      (boundedConstructible_tensorObj hΛ.lisseTensorHypotheses
        (boundedConstructible_singleFunctor_obj Λ Z (-q) P'
          hP'.isConstructibleModuleObject) hL)

variable (Λ) in
/-- The hypotheses on the coefficient ring `Λ` used by the noetherian inductions proving that the
bounded constructible complexes are stable under `⊗ᴸ` and `RHom`: those of
`ProEtale.CondensedRing.LisseTensorHypotheses`, and `RHom(A, L)` is bounded constructible for `A`
bounded with pro-étale locally finitely presented (lisse) cohomology sheaves and `L` bounded
constructible, on schemes with noetherian underlying space. -/
structure LisseHypotheses : Prop extends LisseTensorHypotheses Λ where
  ihom (Z : Scheme.{u}) [TopologicalSpace.NoetherianSpace Z]
    {A L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))}
    (hA : DerivedCategory.TStructure.t.bounded A)
    (hA' : ∀ n, IsLocallyFinitelyPresented (condensedRingObj Λ Z)
      ((DerivedCategory.homologyFunctor _ n).obj A))
    (hL : boundedConstructible (condensedRingObj Λ Z) L) :
    boundedConstructible (condensedRingObj Λ Z) ((ihom A).obj L)

/-- If the locally finitely presented module objects over `Λ` are locally free, the hypotheses
`ProEtale.CondensedRing.LisseHypotheses` hold, by
`ProEtale.CondensedRing.boundedConstructible_ihom_of_isLocallyFree_homology`. -/
theorem TensorHypotheses.lisseHypotheses (hΛ : TensorHypotheses Λ) : LisseHypotheses Λ where
  toLisseTensorHypotheses := hΛ.lisseTensorHypotheses
  ihom Z _ _ _ hA hA' hL :=
    boundedConstructible_ihom_of_isLocallyFree_homology hΛ hA
      (fun n ↦ hΛ.isLocallyFree Z _ (hA' n)) hL

/-- The open piece of the induction step: if the cohomology sheaves of the pullback of `K` to a
surjective closed immersion `c : E ⟶ V` are lisse, then `RHom(K, L)` is bounded constructible on
`V` for every bounded constructible `L`. -/
lemma boundedConstructible_ihom_of_lisse (hΛ : LisseHypotheses Λ) {V E : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace V] (c : E ⟶ V) [IsClosedImmersion c] [Surjective c]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V))}
    (hK : boundedConstructible (condensedRingObj Λ V) K)
    (hKc : ∀ n, IsLocallyFinitelyPresented (condensedRingObj Λ E)
      ((DerivedCategory.homologyFunctor _ n).obj ((L((c)^*⟦Λ⟧)).obj K)))
    (hL : boundedConstructible (condensedRingObj Λ V) L) :
    boundedConstructible (condensedRingObj Λ V) ((ihom K).obj L) := by
  have : TopologicalSpace.NoetherianSpace E := c.isClosedEmbedding.isInducing.noetherianSpace
  -- the closed complement of `c` is empty, so the unit `L ⟶ Rc_* Lc^* L` is an iso
  have : IsEmpty (⊥ : V.Opens).toScheme := ⟨fun x ↦ by obtain ⟨x, hx⟩ := x; exact hx⟩
  have : QuasiCompact (⊥ : V.Opens).ι := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have hc : IsCompl (Set.range c.base) (Set.range (⊥ : V.Opens).ι.base) := by
    rw [Set.range_eq_univ.2 c.surjective, Scheme.Opens.range_ι]
    exact isCompl_top_bot
  have hu := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ
    (⊥ : V.Opens).ι c hc (K := L) (isZero_derivedCategory_of_isEmpty' Λ _)
  have hcK : boundedConstructible (condensedRingObj Λ E) ((L((c)^*⟦Λ⟧)).obj K) :=
    boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ c K hK
  have hcL : boundedConstructible (condensedRingObj Λ E) ((L((c)^*⟦Λ⟧)).obj L) :=
    boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ c L hL
  exact (boundedConstructible _).prop_of_iso
    ((ihom K).mapIso (asIso ((derivedUpperStarLowerStarAdjunction Λ c).unit.app L)) ≪≫
      ihomRightDerivedLowerStarIso Λ c K _).symm
    (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion Λ c
      (hΛ.ihom E hcK.1 hKc hcL))

/-- **The bounded constructible complexes are stable under the derived internal hom**, for a
coefficient ring `Λ` satisfying `ProEtale.CondensedRing.LisseHypotheses`, on a scheme `T` with
noetherian underlying space such that the derived pushforwards along the open immersions into
closed subschemes of `T` preserve bounded constructible complexes. -/
theorem boundedConstructible_ihom (hΛ : LisseHypotheses Λ) {T : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace T]
    (hRj : ∀ (D : Scheme.{u}) (c : D ⟶ T) [IsClosedImmersion c] (V : D.Opens)
      (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
        (condensedRingObj Λ V))), boundedConstructible (condensedRingObj Λ V) A →
        boundedConstructible (condensedRingObj Λ D) ((R((V.ι)_*⟦Λ⟧)).obj A))
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))}
    (hK : boundedConstructible (condensedRingObj Λ T) K)
    (hL : boundedConstructible (condensedRingObj Λ T) L) :
    boundedConstructible (condensedRingObj Λ T) ((ihom K).obj L) := by
  suffices key : ∀ Z : TopologicalSpace.Closeds T, ∀ (D : Scheme.{u}) (c : D ⟶ T)
      [IsClosedImmersion c], Set.range c.base ⊆ Z →
      ∀ K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
        (condensedRingObj Λ D)), boundedConstructible _ K → boundedConstructible _ L →
        boundedConstructible (condensedRingObj Λ D) ((ihom K).obj L) from
    key ⊤ T (𝟙 T) (fun _ _ ↦ trivial) K L hK hL
  intro Z
  induction Z using WellFoundedLT.induction with
  | ind Z ih =>
  intro D c _ hcZ K L hK hL
  have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
  rcases isEmpty_or_nonempty D with hD | hD
  · exact boundedConstructible_of_isZero Λ (isZero_derivedCategory_of_isEmpty' Λ _)
  have := hΛ.isTriangulated D
  obtain ⟨V, E, c', ⟨v, hv⟩, _, _, hc'⟩ := exists_isLocallyFinitelyPresented_homology_upperStar hK
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hij : IsCompl (Set.range V.closedComplement.base) (Set.range V.ι.base) := by
    rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]
    exact isCompl_compl.symm
  -- the triangle `L ⟶ Rj_* Lj^* L ⟶ C ⟶ L[1]`
  obtain ⟨C, v', w, hT⟩ := distinguished_cocone_triangle
    ((derivedUpperStarLowerStarAdjunction Λ V.ι).unit.app L)
  have hjL : boundedConstructible (condensedRingObj Λ D)
      ((R((V.ι)_*⟦Λ⟧)).obj ((L((V.ι)^*⟦Λ⟧)).obj L)) :=
    hRj D c V _ (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ V.ι L hL)
  have hC : boundedConstructible (condensedRingObj Λ D) C :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₃ _ hT hL hjL
  -- `C` is supported on the closed complement of `V`
  have hjC : IsZero ((L((V.ι)^*⟦Λ⟧)).obj C) := by
    have h₁ : IsIso ((L((V.ι)^*⟦Λ⟧)).map
        ((derivedUpperStarLowerStarAdjunction Λ V.ι).unit.app L)) :=
      IsIso.of_isIso_fac_right (hh := IsIso.id _)
        ((derivedUpperStarLowerStarAdjunction Λ V.ι).left_triangle_components L)
    let F := ((V.ι)^*⟦Λ⟧).mapDerivedCategory
    have h₁' : IsIso (F.map ((derivedUpperStarLowerStarAdjunction Λ V.ι).unit.app L)) :=
      (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory Λ V.ι) _).1 h₁
    have hFT := F.map_distinguished _ hT
    exact ((Triangle.isZero₃_iff_isIso₁ _ hFT).2 h₁').of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ V.ι).app C)
  have hu := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ V.ι V.closedComplement
    hij hjC
  -- apply `RHom(K, -)`
  let adj : (curriedTensor _).obj K ⊣ ihom K := ihom.adjunction K
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have : (ihom K).IsTriangulated := adj.isTriangulated_rightAdjoint
  have hT' := (ihom K).map_distinguished _ hT
  refine (boundedConstructible _).ext_of_isTriangulatedClosed₁ _ hT' ?_ ?_
  · -- the open piece
    refine (boundedConstructible _).prop_of_iso (ihomRightDerivedLowerStarIso Λ V.ι K _).symm
      (hRj D c V _ ?_)
    refine boundedConstructible_ihom_of_lisse hΛ c'
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ V.ι K hK) (fun n ↦ ?_)
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ V.ι L hL)
    exact (hc' n).of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
      ((leftDerivedUpperStarComp Λ c' V.ι).app K))
  · -- the closed piece, by induction
    let Z' : TopologicalSpace.Closeds T := ⟨c.base '' Set.range V.closedComplement.base,
      c.isClosedEmbedding.isClosedMap _ V.closedComplement.isClosedEmbedding.isClosed_range⟩
    have hZ' : Z' < Z := by
      refine IsConcreteLE.lt_iff_le_and_exists.2 ⟨fun x ⟨w, _, hw⟩ ↦ hcZ ⟨w, hw⟩,
        c.base v, hcZ ⟨v, rfl⟩, fun ⟨w, hw, hwv⟩ ↦ ?_⟩
      rw [c.isClosedEmbedding.injective hwv, Scheme.Opens.range_closedComplement] at hw
      exact hw hv
    have hrange : Set.range (V.closedComplement ≫ c).base ⊆ Z' := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact subset_rfl
    exact (boundedConstructible _).prop_of_iso
      ((ihom K).mapIso (asIso ((derivedUpperStarLowerStarAdjunction Λ V.closedComplement).unit.app
        C)) ≪≫ ihomRightDerivedLowerStarIso Λ V.closedComplement K _).symm
      (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion Λ V.closedComplement
        (ih Z' hZ' _ (V.closedComplement ≫ c) hrange _ _
          (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ _ K hK)
          (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ _ C hC)))

/-- **The bounded constructible complexes are stable under the derived internal hom**, on a
separated scheme `X` of finite type over a field `k`, for a coefficient ring `Λ` satisfying
`ProEtale.CondensedRing.LisseHypotheses` and such that the derived pushforwards along open
immersions of separated `k`-schemes of finite type preserve bounded constructible complexes
(Deligne's finiteness theorem). -/
theorem boundedConstructible_ihom_of_over (hΛ : LisseHypotheses Λ) {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    (hRf : ∀ (U Y : Over (Spec (.of k))) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
      [IsSeparated U.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      (j : U ⟶ Y) [IsOpenImmersion j.left]
      (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj Λ U.left))), boundedConstructible (condensedRingObj Λ U.left) A →
        boundedConstructible (condensedRingObj Λ Y.left) ((R((j.left)_*⟦Λ⟧)).obj A))
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))}
    (hK : boundedConstructible (condensedRingObj Λ X.left) K)
    (hL : boundedConstructible (condensedRingObj Λ X.left) L) :
    boundedConstructible (condensedRingObj Λ X.left) ((ihom K).obj L) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  refine boundedConstructible_ihom hΛ (fun D c _ V A hA ↦ ?_) hK hL
  have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : LocallyOfFiniteType (Over.mk (V.ι ≫ c ≫ X.hom)).hom := by dsimp; infer_instance
  have : QuasiCompact (Over.mk (V.ι ≫ c ≫ X.hom)).hom := by dsimp; infer_instance
  have : IsSeparated (Over.mk (V.ι ≫ c ≫ X.hom)).hom := by dsimp; infer_instance
  have : LocallyOfFiniteType (Over.mk (c ≫ X.hom)).hom := by dsimp; infer_instance
  have : QuasiCompact (Over.mk (c ≫ X.hom)).hom := by dsimp; infer_instance
  have : IsSeparated (Over.mk (c ≫ X.hom)).hom := by dsimp; infer_instance
  let f : Over.mk (V.ι ≫ c ≫ X.hom) ⟶ Over.mk (c ≫ X.hom) := Over.homMk V.ι rfl
  have : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion V.ι)
  exact hRf _ _ f A hA

end AlgebraicGeometry.ProEtale.CondensedRing
