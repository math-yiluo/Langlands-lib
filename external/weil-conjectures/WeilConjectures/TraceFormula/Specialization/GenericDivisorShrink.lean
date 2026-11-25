/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericDivisorLisse
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorLocal
public import WeilConjectures.TraceFormula.Specialization.OpenExchange

/-!

# Vanishing of the restricted specialization near a point is local

Let `g : V ⟶ X` be an open immersion, `Z = V(I) ⊆ X` and `Z ∩ V = V(g^* I)`. For any coefficient
ring `Λ` and any complex `L` on `X`, if `Le'^* Ψ_V(Lg^* L)` vanishes near a point `ζ'` of
`Z ∩ V`, then `Le^* Ψ_X(L)` vanishes near its image `ζ` in `Z`
(`ProEtale.CondensedRing.nearbyCyclesVanishNear_of_isOpenImmersion`). Indeed the pullback exchange
of the open immersion of deformations is invertible
(`ProEtale.CondensedRing.isIso_deformationModelHom_pullbackExchange`), so
`Le'^* Ψ_V(Lg^* L) ≅ Lg₀^* Le^* Ψ_X(L)` for the open immersion `g₀ : N_⊥(Z ∩ V) ⟶ N_⊥ Z` of zero
sections.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X V : Over (Spec (.of k))} (g : V ⟶ X) [IsOpenImmersion g.left]
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- For an open immersion `g : V ⟶ X`, the restriction to the zero section of the specialization
commutes with the restriction to `V`: `Le'^* Ψ_V(Lg^* L) ≅ Lg₀^* Le^* Ψ_X(L)`. -/
noncomputable def zeroSectionNearbyCyclesUpperStarIso
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    L(((zeroSectionSpecialFibreMap V (I.comap g.left) k').left)^*⟦Λ⟧).obj
        (((deformationModel V (I.comap g.left) k').nearbyCycles Λ).obj
          (L((g.left)^*⟦Λ⟧).obj L)) ≅
      L(((centreSpecialFibreMap g I k').left)^*⟦Λ⟧).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).obj
          (((deformationModel X I k').nearbyCycles Λ).obj L)) :=
  have : IsIso ((comapDeformationModelHom g I k').pullbackExchange Λ) :=
    isIso_deformationModelHom_pullbackExchange g _ k' Λ rfl
  (L(((zeroSectionSpecialFibreMap V (I.comap g.left) k').left)^*⟦Λ⟧)).mapIso
      (asIso (((comapDeformationModelHom g I k').pullbackExchange Λ).app L)).symm ≪≫
    ((leftDerivedUpperStarComp Λ _ _).app _).symm ≪≫
    eqToIso (by rw [zeroSectionSpecialFibreMap_comp_eq]) ≪≫
    (leftDerivedUpperStarComp Λ _ _).app _

/-- **Vanishing near a point is local**: if `Le'^* Ψ_V(Lg^* L)` vanishes near a point `ζ'` of
`Z ∩ V` for an open immersion `g : V ⟶ X`, then `Le^* Ψ_X(L)` vanishes near the image of `ζ'`. -/
theorem nearbyCyclesVanishNear_of_isOpenImmersion
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (ζ' : (centre V (I.comap g.left)).left)
    (h : nearbyCyclesVanishNear V (I.comap g.left) k' Λ ζ' (L((g.left)^*⟦Λ⟧).obj L)) :
    nearbyCyclesVanishNear X I k' Λ ((centreMap g I).left ζ') L := by
  obtain ⟨U', hζU', hU'⟩ := h
  rw [restrictedZeroSectionNearbyCycles_obj] at hU'
  refine ⟨(centreMap g I).left ''ᵁ U', ⟨ζ', hζU', rfl⟩, ?_⟩
  rw [restrictedZeroSectionNearbyCycles_obj]
  exact isZero_leftDerivedUpperStar_ι_obj_of_le Λ
    (centreSpecialFibreMap_image_preimage k' I g U').ge
    (isZero_leftDerivedUpperStar_image_ι_obj Λ _ _
      (hU'.of_iso (Functor.mapIso _ (zeroSectionNearbyCyclesUpperStarIso g I k' Λ L).symm)))

end AlgebraicGeometry.ProEtale.CondensedRing
