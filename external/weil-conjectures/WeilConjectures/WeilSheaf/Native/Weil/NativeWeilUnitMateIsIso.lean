/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRingedTensorModel
import WeilConjectures.WeilSheaf.Native.NativeHomRepresentativeUniqueness
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Pointwise invertibility of the native tensor unit mate

Source: native tensor lift, comparison on flat representatives; Stacks 06YS and 08J9.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

private theorem unit_mate_isIso_of_tensor_model
    {C D : Type*} [Category* C] [Category* D]
    {H : Cᵒᵖ × C ⥤ C} {H' : Dᵒᵖ × D ⥤ D}
    (W : CoefficientClosedStructure H) (S : CoefficientClosedStructure H')
    (F : C ⥤ D) (χ : H ⋙ F ≅ F.op.prod F ⋙ H')
    (t : W.tensor ⋙ F ≅ F.prod F ⋙ S.tensor)
    (ht : ∀ A K, t.inv.app (A, K) =
      (S.transpose (F.obj A) (F.obj K) (F.obj (W.tensor.obj (A, K)))).symm
        (F.map ((W.adjunction K).unit.app A) ≫ χ.hom.app (op K, W.tensor.obj (A, K))))
    (K : C) (L : C ⥤ C) (a : L ⊣ Prod.sectR (op K) C ⋙ H) (A : C) :
    IsIso ((S.transpose (F.obj A) (F.obj K) (F.obj (L.obj A))).symm
      (F.map (a.unit.app A) ≫ χ.hom.app (op K, L.obj A))) := by
  let e := (W.adjunction K).leftAdjointUniq a
  have hu := (W.adjunction K).unit_leftAdjointUniq_hom_app a A
  change (W.adjunction K).unit.app A ≫
    H.map (Prod.mkHom (𝟙 (op K)) (e.hom.app A)) = a.unit.app A at hu
  have hn := χ.hom.naturality (Prod.mkHom (𝟙 (op K)) (e.hom.app A))
  have hn' :
      F.map
          (H.map (Prod.mkHom (𝟙 (op K)) (e.hom.app A))) ≫
          χ.hom.app (op K, L.obj A) =
        χ.hom.app (op K, W.tensor.obj (A, K)) ≫
          H'.map (Prod.mkHom (𝟙 (op (F.obj K)))
            (F.map (e.hom.app A))) := by
    simpa [CoefficientClosedStructure.tensor] using hn
  have hm :
      (S.transpose (F.obj A) (F.obj K)
        (F.obj (L.obj A))).symm
          (F.map (a.unit.app A) ≫ χ.hom.app (op K, L.obj A)) =
        t.inv.app (A, K) ≫ F.map (e.hom.app A) := by
    rw [← hu, Functor.map_comp, Category.assoc]
    erw [hn']
    rw [← Category.assoc]
    exact ((S.adjunction (F.obj K)).homEquiv_naturality_right_symm
      (F.map ((W.adjunction K).unit.app A) ≫
        χ.hom.app (op K, W.tensor.obj (A, K)))
      (F.map (e.hom.app A))).trans
        (congrArg (fun f ↦ f ≫ F.map (e.hom.app A)) (ht A K).symm)
  rw [hm]
  infer_instance

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- For any left adjoint of a fixed-source native derived Hom, the ordinary
transpose of the forgotten unit is invertible. The assertion is about one
arrow; it supplies no bifunctor, natural transformation or adjoint existence.

Source: prose-10-20, internal-Hom/transposition paragraph;
native tensor lift step 2; Stacks Tags 06YS, 08J9 and 0A97
(blueprint: lem-sf-native-weil-unit-mate-iso).

Proof: compute the adjunction for a flat-term K-flat representative of K on
the Frobenius ringed action site. Forgetting preserves such resolutions and
K-injective targets. On a K-flat representative of A and a K-injective target,
the native product-total Hom comparison is fixed on each projection by hη.
The ordinary model normalization hS uncurries this comparison to the identity
on each summand of the underived relative tensor. The native-to-standard
row signs occur on both sides and cancel. Consequently the mate for this
resolution-defined left adjoint is the localized identity comparison of the
two total tensors and is an isomorphism. Source and target replacement
compatibilities extend this conclusion to arbitrary derived A and K.
Finally compare any supplied L ⊣ M.weilHom(K,-) with the resolution-defined
adjoint by uniqueness of left adjoints. The unit identity for that unique
isomorphism and naturality of η express the displayed mate as the canonical
mate followed by the forgotten adjoint isomorphism. Both factors are
invertible. Thus the assertion holds for every choice of adjunction, without
requiring normalization of that choice. The argument also applies to zero
objects and the empty scheme. -/
theorem native_weil_unit_mate_isIso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (η : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hη : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β)
    (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (L : DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤
      DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (a : L ⊣ Prod.sectR (op K) _ ⋙ M.weilHom)
    (A : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    IsIso ((S.transpose ((nativeForget k₀ l X).obj A) ((nativeForget k₀ l X).obj K)
      ((nativeForget k₀ l X).obj (L.obj A))).symm
        ((nativeForget k₀ l X).map (a.unit.app A) ≫ η.hom.app (op K, L.obj A))) := by
  obtain ⟨W, γ, δ, ε, t, χ, c, hc, hχ, ht⟩ :=
    native_weil_ringed_tensor_model k₀ l X M S β hmonoidal hS
  have hηχ := native_hom_representative_unique k₀ l X M η hη χ hχ
  subst η
  exact unit_mate_isIso_of_tensor_model W S (nativeForget k₀ l X) χ t ht K L a A

end AlgebraicGeometry.ProEtaleWeilSheaf
