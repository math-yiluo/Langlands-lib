/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierMul
public import WeilConjectures.SixFunctors.ProEtale.Adic.TensorLeftInvertible
public import WeilConjectures.WeilSheaf.ArtinSchreierTrivialization

/-!
# Multiplicativity of the Artin–Schreier sheaves on the geometric fibre

For global functions `a, b` on a `k₀`-scheme `X`, the underlying sheaves on `X̄` satisfy
`ℒ_{ψ,a} ≅ 𝓗om(ℒ_{ψ,b}, ℒ_{ψ,a+b})`
(`AlgebraicGeometry.nonempty_iso_ihom_upperStar_artinSchreier_of_eq`), and `ℒ_ψ` pulled back to
any scheme over `𝔸¹_{k̄}` becomes trivial over the base change of the geometric Artin–Schreier
covering, so that `𝓗om(h^* ℒ_ψ, N) ⊗ h^* ℒ_ψ ≅ N`
(`AlgebraicGeometry.nonempty_tensorLeft_ihom_upperStar_artinSchreier`). Together they give
`ℒ_{ψ,a} ⊗ ℒ_{ψ,b} ≅ ℒ_{ψ,a+b}` for the underlying sheaves (blueprint
`lemma-artin-schreier-character-sheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance high] WeilSheaf.hasImage_artinSchreierIdempotent

omit [Finite k₀] in
/-- A morphism `g : X ⟶ 𝔸¹` over `k₀` is the morphism defined by its coordinate function. -/
lemma affineLine.eq_homOfSection {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (g : X ⟶ affineLine k₀) [g.IsOver (Spec (CommRingCat.of k₀))] :
    g = affineLine.homOfSection k₀ (g.appTop (AffineSpace.coord _ PUnit.unit)) := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · rw [affineLine.homOfSection, AffineSpace.homOfVector_over]
    exact comp_over g _
  · rw [affineLine.homOfSection, AffineSpace.homOfVector_appTop_coord]

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
/-- An isomorphism `A ≅ 𝓗om(B, C)` of pro-étale Weil sheaves gives one of the underlying sheaves
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.nonempty_carrier_iso_ihom_of_iso {A B C : ProEtaleWeilSheaf k₀ l X}
    (e : A ≅ ProEtaleWeilSheaf.ihom k₀ l X B C) :
    Nonempty (A.carrier ≅ (ProEtale.AdicSheaf.ihom B.carrier).obj C.carrier) :=
  ⟨(Endofunctor.IsoAlgebra.forget _).mapIso e⟩

/-- `ℒ_{ψ,a} ≅ 𝓗om(ℒ_{ψ,b}, ℒ_{ψ,a+b})` for the underlying sheaves on `X̄`, for global functions
`a, b` on `X` (blueprint `lemma-artin-schreier-character-sheaf`). -/
theorem nonempty_iso_ihom_carrier_artinSchreierOf (ψ : AddChar k₀ (PadicAlgCl l))
    (a b : Γ(X, ⊤)) :
    Nonempty ((artinSchreierOf ψ a).obj.carrier ≅ (ProEtale.AdicSheaf.ihom
      (artinSchreierOf ψ b).obj.carrier).obj (artinSchreierOf ψ (a + b)).obj.carrier) := by
  set f : planeIndex → Γ(X, ⊤) := fun i ↦ ![a, b] i.down with hf
  have hv (x y : k₀) (z : Γ(X, ⊤))
      (hz : z = (X ↘ Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom x) * a +
        (X ↘ Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom y) * b) :
      affineLine.homOfSection k₀ z ≫ affineLine.smul k₀ 1 =
        planeLinearFunction k₀ f (fun i ↦ ![x, y] i.down) := by
    rw [hf, planeLinearFunction_pair, affineLine.homOfSection_comp_smul, hz]
    simp
  obtain ⟨ea⟩ := nonempty_iso_artinSchreierOf_obj ψ a (hv 1 0 a (by simp))
  obtain ⟨eb⟩ := nonempty_iso_artinSchreierOf_obj ψ b (hv 0 1 b (by simp))
  obtain ⟨eab⟩ := nonempty_iso_artinSchreierOf_obj ψ (a + b) (hv 1 1 (a + b) (by simp))
  have h (g : planeIndex → k₀) : ψ (∑ i, ![1, 0] i.down * g i) *
      ψ (∑ i, ![0, 1] i.down * g i) = ψ (∑ i, ![1, 1] i.down * g i) := by
    rw [← AddChar.map_add_eq_mul, sum_planeIndex, sum_planeIndex, sum_planeIndex]
    congr 1
    simp
  obtain ⟨e⟩ := nonempty_iso_ihom_artinSchreierPlane f ψ ψ ψ
    (fun i ↦ ![1, 0] i.down) (fun i ↦ ![0, 1] i.down) (fun i ↦ ![1, 1] i.down) h
  exact ProEtaleWeilSheaf.nonempty_carrier_iso_ihom_of_iso (ea ≪≫ e ≪≫
    ProEtaleWeilSheaf.ihomMapIsoLeft eb _ ≪≫ ProEtaleWeilSheaf.ihomMapIsoRight _ eab.symm)

/-- The underlying sheaf of `ℒ_{ψ,a}` is the pullback of that of `ℒ_ψ` along `ā : X̄ ⟶ 𝔸¹_{k̄}`. -/
theorem artinSchreierOf_obj_carrier (ψ : AddChar k₀ (PadicAlgCl l)) (a : Γ(X, ⊤)) :
    (artinSchreierOf ψ a).obj.carrier =
      (Scheme.Hom.geometricFiberMap (affineLine.homOfSection k₀ a) (comp_over _ _))^*ᵃ[l].obj
        (artinSchreier ψ 1).obj.carrier := by
  rw [artinSchreierOf_eq, WeilSheaf.upperStar_obj_obj_carrier]

/-- `ḡ₁^* ℒ_ψ ≅ 𝓗om(ḡ₂^* ℒ_ψ, ḡ₃^* ℒ_ψ)` on `X̄` for morphisms `g₁, g₂, g₃ : X ⟶ 𝔸¹` given by
functions `a`, `b` and `a + b` (blueprint `lemma-artin-schreier-character-sheaf`). -/
theorem nonempty_iso_ihom_upperStar_artinSchreier_of_eq (ψ : AddChar k₀ (PadicAlgCl l))
    (a b : Γ(X, ⊤)) (g₁ g₂ g₃ : X ⟶ affineLine k₀) [g₁.IsOver (Spec (CommRingCat.of k₀))]
    [g₂.IsOver (Spec (CommRingCat.of k₀))] [g₃.IsOver (Spec (CommRingCat.of k₀))]
    (h₁ : g₁ = affineLine.homOfSection k₀ a) (h₂ : g₂ = affineLine.homOfSection k₀ b)
    (h₃ : g₃ = affineLine.homOfSection k₀ (a + b)) :
    Nonempty ((Scheme.Hom.geometricFiberMap g₁ (comp_over _ _))^*ᵃ[l].obj
        (artinSchreier ψ 1).obj.carrier ≅
      (ProEtale.AdicSheaf.ihom ((Scheme.Hom.geometricFiberMap g₂ (comp_over _ _))^*ᵃ[l].obj
        (artinSchreier ψ 1).obj.carrier)).obj
        ((Scheme.Hom.geometricFiberMap g₃ (comp_over _ _))^*ᵃ[l].obj
          (artinSchreier ψ 1).obj.carrier)) := by
  obtain ⟨e⟩ := nonempty_iso_ihom_carrier_artinSchreierOf ψ a b
  rw [artinSchreierOf_obj_carrier, artinSchreierOf_obj_carrier,
    artinSchreierOf_obj_carrier] at e
  have c₁ : Scheme.Hom.geometricFiberMap g₁ (comp_over g₁ (Spec (CommRingCat.of k₀))) =
      Scheme.Hom.geometricFiberMap (affineLine.homOfSection k₀ a) (comp_over _ _) := by
    subst h₁
    rfl
  have c₂ : Scheme.Hom.geometricFiberMap g₂ (comp_over g₂ (Spec (CommRingCat.of k₀))) =
      Scheme.Hom.geometricFiberMap (affineLine.homOfSection k₀ b) (comp_over _ _) := by
    subst h₂
    rfl
  have c₃ : Scheme.Hom.geometricFiberMap g₃ (comp_over g₃ (Spec (CommRingCat.of k₀))) =
      Scheme.Hom.geometricFiberMap (affineLine.homOfSection k₀ (a + b)) (comp_over _ _) := by
    subst h₃
    rfl
  exact ⟨(ProEtale.adicUpperStarCongr l c₁).app _ ≪≫ e ≪≫
    (Mod.ihomMapIso ((ProEtale.adicUpperStarCongr l c₂).app _)).app _ ≪≫
    (ProEtale.AdicSheaf.ihom _).mapIso ((ProEtale.adicUpperStarCongr l c₃).app _).symm⟩

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀
local notation "Ā" => Scheme.Hom.geometricFiber (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

omit [Fact (ringChar k₀ ≠ l)] in
/-- If `π ≫ h ≫ s = q ≫ g` and `g^* F` is trivial, then so is `π^* h^* s^* F`. -/
lemma ProEtale.nonempty_upperStar_upperStar_upperStar_iso_unit {P Y A A' B : Scheme.{u}}
    (π : P ⟶ Y) (h : Y ⟶ A) (s : A ⟶ A') (q : P ⟶ B) (g : B ⟶ A') (hc : π ≫ h ≫ s = q ≫ g)
    (F : ProEtale.AdicSheaf l A') (t : ProEtale.AdicSheaf.unit l B ≅ (g)^*ᵃ[l].obj F) :
    Nonempty ((π)^*ᵃ[l].obj ((h)^*ᵃ[l].obj ((s)^*ᵃ[l].obj F)) ≅ ProEtale.AdicSheaf.unit l P) :=
  ⟨(ProEtale.adicUpperStar l π).mapIso ((ProEtale.adicUpperStarComp l h s).app F).symm ≪≫
    ((ProEtale.adicUpperStarComp l π (h ≫ s)).app F).symm ≪≫
    (ProEtale.adicUpperStarCongr l hc).app F ≪≫ (ProEtale.adicUpperStarComp l q g).app F ≪≫
    (ProEtale.adicUpperStar l q).mapIso t.symm ≪≫ ProEtale.adicUpperStarUnitIso l q⟩

/-- For `h : Y ⟶ 𝔸¹_{k̄}`, the sheaf `h^* ℒ_ψ` becomes trivial on the base change along `h` of the
geometric Artin–Schreier covering `ĀS` (blueprint `lemma-artin-schreier-character-sheaf`). -/
theorem nonempty_upperStar_upperStar_artinSchreier_iso_unit (ψ : AddChar k₀ (PadicAlgCl l))
    {Y : Scheme.{u}} (h : Y ⟶ Ā) :
    Nonempty ((pullback.fst (h ≫ Scheme.Hom.geometricFiberMap (affineLine.smul k₀ 1)
        (comp_over _ _)) ĀS)^*ᵃ[l].obj ((h)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier) ≅
      ProEtale.AdicSheaf.unit l _) := by
  rw [artinSchreier_eq_upperStar_image, WeilSheaf.upperStar_obj_obj_carrier]
  exact ProEtale.nonempty_upperStar_upperStar_upperStar_iso_unit _ h _ _ _
    (pullback.condition (f := h ≫ Scheme.Hom.geometricFiberMap (affineLine.smul k₀ 1)
        (comp_over _ _)) (g := ĀS)) _
    ((affineLine.artinSchreierTrivialization l ψ).trans
      ((ProEtale.adicUpperStar l ĀS).mapIso (affineLine.artinSchreierCarrierIso ψ)).symm)

/-- Tensoring with `h^* ℒ_ψ` inverts `𝓗om(h^* ℒ_ψ, -)`: `𝓗om(h^* ℒ_ψ, N) ⊗ h^* ℒ_ψ ≅ N`, as
`h^* ℒ_ψ` is trivial on a quasi-compact surjective étale covering
(blueprint `lemma-artin-schreier-character-sheaf`). -/
theorem nonempty_tensorLeft_ihom_upperStar_artinSchreier (ψ : AddChar k₀ (PadicAlgCl l))
    {Y : Scheme.{u}} (h : Y ⟶ Ā) (N : ProEtale.AdicSheaf l Y) :
    Nonempty ((Mod.tensorLeft ((h)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier)).obj
      ((ProEtale.AdicSheaf.ihom ((h)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier)).obj N) ≅ N) := by
  obtain ⟨e⟩ := nonempty_upperStar_upperStar_artinSchreier_iso_unit (l := l) ψ h
  exact ⟨ProEtale.AdicSheaf.tensorLeftIhomIso _ e N⟩

end AlgebraicGeometry
