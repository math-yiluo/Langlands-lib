/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFormula

/-!

# The Künneth map of nearby cycles on a slice

Let `P` be the product over `S = Spec k'⟦t⟧` of models `M`, `N` of finite type and `b` a
coordinate of `M`. The restrictions of the nearby cycles of `M`, `N` and `P` to the special fibre
`s'` of the geometric slice are compared with the nearby cycles of the slice of `M` along `b`, of
the change of trait of `N`, and of the slice of `P` along `φ₁ ≫ b`, by the pullback exchanges of
the projections from the base changes (the identifications (E.2) and invariance under change of
trait). This file shows that, under these identifications, the restriction of the Künneth map
`Π_{A,B}` over `s'` is the Künneth map of the slices.

## Main results

* `NearbyCyclesModel.map_kunnethMap_sliceSpecial_comp_pullbackExchange`: the restriction of
  `Π_{A,B}` over `s'`, followed by the exchange of the slice of `P`, is the Künneth map of the
  geometric slice precomposed with the exchanges of the slice of `M` and the change of trait
  of `N`, up to the tensor and pullback comparisons (blueprint `lemma-kunneth-map-slice`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme



variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k' : Type u} [Field k'] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

set_option maxHeartbeats 800000 in
-- the statement involves the Künneth maps of the product and of its slice, whose instances
-- on module objects over the slice need a long search
/-- **The Künneth map on a slice** (blueprint `lemma-kunneth-map-slice`): for the product `P`
over the trait `S = Spec k'⟦t⟧` of models `M`, `N` of finite type and a coordinate `b` of `M`,
identify the restrictions over the special fibre `s'` of the geometric slice of the nearby cycles
of `A`, `B` and `A ⊠ B` with the nearby cycles of the slice of `M` along `b`, of the change of
trait of `N` and of the slice of `P` along `φ₁ ≫ b`, through the pullback exchanges of the
projections (the identifications (E.2) for `b`, invariance under change of trait, and (E.2) for
`b ∘ pr₁`). Then the restriction of `Π_{A,B}` over `s'` is the Künneth map `Π_{A',B'}` of the
geometric slice (`NearbyCyclesModel.sliceFst`, `NearbyCyclesModel.sliceSnd`), up to the tensor
and pullback comparisons. -/
lemma map_kunnethMap_sliceSpecial_comp_pullbackExchange (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦Λ⟧).map
          (kunnethMap Λ φ₁ φ₂ A B) ≫
        ((baseChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
          (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k'))).pullbackExchange
            Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) ≫
        ((baseChange hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
          (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k'))).nearbyCycles
            Λ).map (Functor.OplaxMonoidal.δ L((𝟙 Z)^*⟦Λ⟧) _ _ ≫
          ((pullbackSquareComparison Λ
              (⟨(Category.comp_id f₁).trans (Category.id_comp f₁).symm⟩ :
                CommSq f₁ (𝟙 Z) (𝟙 X) f₁)).hom.app A ⊗ₘ
            (pullbackSquareComparison Λ
              (⟨(Category.comp_id f₂).trans (Category.id_comp f₂).symm⟩ :
                CommSq f₂ (𝟙 Z) (𝟙 Y) f₂)).hom.app B)) =
      Functor.OplaxMonoidal.δ L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
          (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦Λ⟧) _ _ ≫
        (((pullbackSquareComparison Λ
              (⟨Hom.baseChangeSpecial_comp hM hP _ _ _ _ φ₁ _ _ _⟩ :
                CommSq (φ₁.baseChangeSpecial (𝟙 _) (Category.comp_id (φ₁.total ≫ b))
                  (Category.comp_id (traitSlice (traitSliceCoord k'))))
                  (baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
                    (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))
                  (baseChangeSpecialMap hM b hb (traitSlice (traitSliceCoord k'))
                    (traitSlice_over (traitSliceCoord k'))) f₁')).hom.app
            ((M.nearbyCycles Λ).obj A) ≫
              L((φ₁.baseChangeSpecial (𝟙 _) (Category.comp_id (φ₁.total ≫ b))
                  (Category.comp_id (traitSlice (traitSliceCoord k'))))^*⟦Λ⟧).map
              (((baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
                (traitSlice_over (traitSliceCoord k'))).pullbackExchange Λ).app A)) ⊗ₘ
          ((pullbackSquareComparison Λ
              (⟨Hom.baseChangeSpecial_comp hN hP _ _ _ _ φ₂ _ _ _⟩ :
                CommSq (φ₂.baseChangeSpecial (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
                    (comp_coordinate_fst_eq hpb hb) (traitSlice_over (traitSliceCoord k')))
                  (baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
                    (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))
                  (baseChangeSpecialMap hN qN (Category.comp_id qN)
                    (traitMap k' (traitSliceField k')) (Category.comp_id _)) f₂')).hom.app
            ((N.nearbyCycles Λ).obj B) ≫
              L((φ₂.baseChangeSpecial (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
                (comp_coordinate_fst_eq hpb hb) (traitSlice_over (traitSliceCoord k')))^*⟦Λ⟧).map
              (((baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
                (Category.comp_id _)).pullbackExchange Λ).app B))) ≫
        kunnethMap Λ (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb)
          (L((𝟙 X)^*⟦Λ⟧).obj A) (L((𝟙 Y)^*⟦Λ⟧).obj B) := by
  have h := map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ (sliceFst hM hP hb)
      (sliceSnd hN hpb hP hgen hb)
      (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k')))
      (baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
        (Category.comp_id _))
      (baseChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k')))
      (Hom.baseChange_total_comp hM hP _ _ _ _ φ₁ _ _ _ rfl)
      (Hom.baseChange_generic_comp hM hP _ _ _ _ φ₁ _ _ _ rfl)
      (Hom.baseChange_total_comp hN hP _ _ _ _ φ₂ _ _ _ hgen.symm)
      (Hom.baseChange_generic_comp hN hP _ _ _ _ φ₂ _ _ _ hgen.symm)
      ((Category.comp_id f₁).trans (Category.id_comp f₁).symm)
      (Hom.baseChangeSpecial_comp hM hP _ _ _ _ φ₁ _ _ _)
      ((Category.comp_id f₂).trans (Category.id_comp f₂).symm)
      (Hom.baseChangeSpecial_comp hN hP _ _ _ _ φ₂ _ _ _) A B
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
