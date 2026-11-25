/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.Tensor
public import WeilConjectures.WeilSheaf.WeilGroupArithmetic

/-!
# Weil fundamental representations of twists and of pulled-back sheaves

Let `B = (t, β)` be base point data on the geometric fibre `p : X ⟶ X₀` of a scheme over a
finite field, `M` a monodromy of lisse sheaves on `X`. This file computes the Weil fundamental
representation `ρ_F` of `π₁(X, t) ⋊ ℤ`
(`AlgebraicGeometry.FrobeniusBasePoint.WeilData.fundamentalRep`) in two cases:

* constant twists: `ρ_{F ⊗ 𝓑_b} = ρ_F ⊗ b^{deg}`
  (`AlgebraicGeometry.FrobeniusBasePoint.WeilData.fundamentalRep_constantTwist`), since the
  Frobenius of `F ⊗ 𝓑_b` is `b` times that of `F`;
* sheaves pulled back from the model: for a monodromy `M₀` on `X₀` compatible with `M` along `p`
  and a lisse sheaf `H` on `X₀`, the Weil fundamental representation of `p^* H` with its
  canonical Weil structure is the restriction of the monodromy representation of `π₁(X₀, t ≫ p)`
  on `H_{t ≫ p} = (p^* H)_t` along `arithHom : π₁(X, t) ⋊ ℤ → π₁(X₀, t ≫ p)`
  (`AlgebraicGeometry.FrobeniusBasePoint.fundamentalRep_geometricFiberPullback`).

Moreover lisse Weil sheaves with isomorphic Weil fundamental representations are isomorphic
(`AlgebraicGeometry.FrobeniusBasePoint.WeilData.nonempty_iso_of_linearEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open ProEtale Scheme.FiniteEtale

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- Multiplication by a scalar `c` on a lisse sheaf acts on its stalks as multiplication
by `c`. -/
lemma lisseStalk_map_homMk_smul (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y)
    (c : ULift.{u + 1} (PadicAlgCl l)) :
    (lisseStalk l y).map (ObjectProperty.homMk (AdicSheaf.smul c G.obj) : G ⟶ G) = c • 𝟙 _ := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of (AlgebraicClosure Ω))))
      (WeilCoefficients.{u} l)).Linear (ULift.{u + 1} (PadicAlgCl l)) :=
    (constantSheafΓAdj _ _).right_adjoint_linear
  have hy : (y)^*[WeilCoefficients.{u} l].map (c • 𝟙 G.obj.X) = c • 𝟙 _ := by
    have := congrArg Mod.Hom.hom (AdicSheaf.adicUpperStar_map_smul y c G.obj)
    rw [adicUpperStar_map_hom, AdicSheaf.smul_hom, AdicSheaf.smul_hom] at this
    exact this
  change (Sheaf.Γ _ _).map ((y)^*[WeilCoefficients.{u} l].map (AdicSheaf.smul c G.obj).hom) = _
  rw [AdicSheaf.smul_hom, hy, Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

end ProEtale

namespace FrobeniusBasePoint

variable {K : Type u} [Field K] [Finite K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) (B : FrobeniusBasePoint K X)

/-- The Weil structure of a constant twist `F ⊗ 𝓑_b`, as an isomorphism of lisse sheaves
`Fr^* F ≅ F`, is `b` times that of `F`. -/
lemma lisseFrobStr_constantTwist_hom (F : WeilSheaf K l X) (hF : F.IsLisse)
    (b : (PadicAlgCl l)ˣ) :
    ((F.constantTwist b).lisseFrobStr hF).hom = (F.lisseFrobStr hF).hom ≫
      (ObjectProperty.homMk (AdicSheaf.smul (ULift.up (b : PadicAlgCl l)) F.obj.carrier) :
        F.toLisse hF ⟶ F.toLisse hF) := by
  apply ObjectProperty.hom_ext
  simp only [WeilSheaf.lisseFrobStr, Functor.FullyFaithful.preimageIso_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    ObjectProperty.ι_obj, WeilSheaf.adicFrobStr, Iso.trans_hom, Iso.app_hom, Category.assoc]
  -- stated for a variable isomorphism `α`: unfolding the concrete one is expensive
  have h {P Q : AdicSheaf l (X ↘ Spec (.of K)).geometricFiber ⥤
      AdicSheaf l (X ↘ Spec (.of K)).geometricFiber} (α : P ≅ Q) :
      α.hom.app (F.constantTwist b).obj.carrier = α.hom.app F.obj.carrier := rfl
  rw [WeilSheaf.constantTwist_obj_str_hom, h]

/-- The Frobenius `Φ` of the stalk of a constant twist `F ⊗ 𝓑_b` is `b` times that of `F`. -/
lemma frobStalk_constantTwist (F : WeilSheaf K l X) (hF : F.IsLisse) (b : (PadicAlgCl l)ˣ)
    (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    frobStalk M B (F.constantTwist b) hF v = (b : PadicAlgCl l) • frobStalk M B F hF v := by
  rw [frobStalk_apply, frobStalk_apply, lisseFrobStr_constantTwist_hom, Functor.map_comp,
    lisseStalk_map_homMk_smul]
  rfl

namespace WeilData

variable {B} {W : Type*} [Group W] (D : B.WeilData W)

open Representation in
/-- **The Weil fundamental representation of a constant twist** `F ⊗ 𝓑_b` is the twist
`ρ_F ⊗ b^{deg}` of that of `F`: the geometric parts agree, and the Frobenius `Φ` is multiplied
by `b`. -/
theorem fundamentalRep_constantTwist (F : WeilSheaf K l X) (hF : F.IsLisse)
    (b : (PadicAlgCl l)ˣ) (w : W) (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    D.fundamentalRep M (F.constantTwist b) hF w v =
      (D.fundamentalRep M F hF).twist (degreeCharacter D.deg b) w v := by
  refine D.intertwines_of_geometric_frobLift (D.fundamentalRep M (F.constantTwist b) hF)
    ((D.fundamentalRep M F hF).twist (degreeCharacter D.deg b)) LinearMap.id
    (fun u hu v ↦ ?_) (fun v ↦ ?_) w v
  · rw [twist_apply, degreeCharacter_apply, MonoidHom.mem_ker.1 hu, toAdd_one, zpow_zero,
      Units.val_one, one_smul, D.fundamentalRep_geometric M F hF ⟨u, hu⟩,
      D.fundamentalRep_geometric M (F.constantTwist b) hF ⟨u, hu⟩]
    rfl
  · rw [twist_apply, degreeCharacter_apply, D.deg_frobLift, toAdd_ofAdd, zpow_one,
      LinearMap.smul_apply, fundamentalRep_frobLift, fundamentalRep_frobLift]
    exact frobStalk_constantTwist M B F hF b v

/-- **Lisse Weil sheaves with isomorphic Weil fundamental representations are isomorphic**, if
the monodromy at the base point is an equivalence: a linear isomorphism of stalks intertwining
the Weil fundamental representations is the stalk of an isomorphism (fullness and faithfulness,
`AlgebraicGeometry.FrobeniusBasePoint.WeilData.exists_stalkMap_eq`). -/
theorem nonempty_iso_of_linearEquiv (hM : M.IsEquivalenceAt B.t) {F G : WeilSheaf K l X}
    (hF : F.IsLisse) (hG : G.IsLisse)
    (e : LisseMonodromy.StalkSpace B.t (F.toLisse hF) ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (G.toLisse hG))
    (he : ∀ w v, e (D.fundamentalRep M F hF w v) = D.fundamentalRep M G hG w (e v)) :
    Nonempty (F ≅ G) := by
  obtain ⟨f, hf⟩ := D.exists_stalkMap_eq M hM (F := ⟨F, hF⟩) (G := ⟨G, hG⟩) e.toLinearMap he
  obtain ⟨g, hg⟩ := D.exists_stalkMap_eq M hM (F := ⟨G, hG⟩) (G := ⟨F, hF⟩) e.symm.toLinearMap
    fun w v ↦ by
      rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  have h₁ : f ≫ g = 𝟙 _ := stalkMap_injective M B hM _ _ (by
    rw [ObjectProperty.FullSubcategory.comp_hom, B.stalkMap_comp _ _ hF hG hF, hf, hg,
      ObjectProperty.FullSubcategory.id_hom, stalkMap_id]
    ext v
    simp)
  have h₂ : g ≫ f = 𝟙 _ := stalkMap_injective M B hM _ _ (by
    rw [ObjectProperty.FullSubcategory.comp_hom, B.stalkMap_comp _ _ hG hF hG, hf, hg,
      ObjectProperty.FullSubcategory.id_hom, stalkMap_id]
    ext v
    simp)
  exact ⟨⟨f.hom, g.hom, congrArg (fun φ ↦ φ.hom) h₁, congrArg (fun φ ↦ φ.hom) h₂⟩⟩

open Representation in
/-- A constant twist `F ⊗ 𝓑_b` of a lisse Weil sheaf is isomorphic to `G` as soon as the twist
`ρ_F ⊗ b^{deg}` of the Weil fundamental representation of `F` is isomorphic to that of `G`. -/
theorem nonempty_constantTwist_iso_of_linearEquiv (hM : M.IsEquivalenceAt B.t)
    {F G : WeilSheaf K l X} (hF : F.IsLisse) (hG : G.IsLisse) (b : (PadicAlgCl l)ˣ)
    (e : LisseMonodromy.StalkSpace B.t (F.toLisse hF) ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (G.toLisse hG))
    (he : ∀ w v, e ((D.fundamentalRep M F hF).twist (degreeCharacter D.deg b) w v) =
      D.fundamentalRep M G hG w (e v)) :
    Nonempty (F.constantTwist b ≅ G) :=
  D.nonempty_iso_of_linearEquiv M hM hF hG e fun w v ↦ by
    rw [fundamentalRep_constantTwist]
    exact he w v

end WeilData

end FrobeniusBasePoint

end AlgebraicGeometry
