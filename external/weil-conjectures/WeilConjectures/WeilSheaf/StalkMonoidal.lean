/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.SectionsMonoidal
public import WeilConjectures.WeilSheaf.Stalk

/-!
# The Frobenius of the stalks of Weil sheaves is monoidal

For a geometric point `s : Spec k̄ ⟶ X̄`, the stalk functor `G ↦ G_s = Γ(Spec k̄, s^* G)` on
pro-étale sheaves of `ℚ̄_ℓ`-modules on `X̄` is lax monoidal, as the composite of the monoidal
pullback `s^*` and the lax monoidal global sections. If `s ≫ Frᵐ = σᵐ ≫ s`, the identification

`G_s ≅ G_{σᵐ ≫ s} = G_{s ≫ Frᵐ} ≅ ((Frᵐ)^* G)_s ≅ ((Fr⁻ᵐ)_* G)_s`

is a natural isomorphism `G_s ≅ ((Fr⁻ᵐ)_* G)_s` of lax monoidal functors of `G`
(`AlgebraicGeometry.WeilSheaf.stalkFrobeniusIso`), monoidal since all its constituents are.
The Frobenius of the stalk of a Weil sheaf `F` is this isomorphism followed by the stalk of the
iterated Weil structure `φ_m : (Fr⁻ᵐ)_* F ≅ F`
(`AlgebraicGeometry.WeilSheaf.stalkAt_frobenius_eq_stalkFrobeniusIso`).

Consequently, a morphism `e : D ⊗ F ⟶ A` of underlying sheaves compatible with the iterated
Weil structures induces a pairing of the stalks `D_s ⊗ F_s ⟶ A_s` compatible with the
Frobenius of the stalks (`AlgebraicGeometry.WeilSheaf.stalkPairing_frobenius`).

## Main definitions

- `AlgebraicGeometry.WeilSheaf.stalkSheafFunctor`: the stalk functor `G ↦ G_s` on sheaves.
- `AlgebraicGeometry.WeilSheaf.stalkFrobeniusIso`: the monoidal isomorphism
  `G_s ≅ ((Fr⁻ᵐ)_* G)_s`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- The stalk functor `G ↦ G_s = Γ(Spec k̄, s^* G)` at a geometric point `s` of `X̄`, on
pro-étale sheaves of `ℚ̄_ℓ`-modules. It is lax monoidal. -/
noncomputable abbrev stalkSheafFunctor
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) ⥤ WeilCoefficients.{u} l :=
  (s)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _

variable (k₀ l X) in
/-- The isomorphism `G_{σᵐ ≫ s} ≅ G_s` of stalk functors: pullback along `σᵐ ≫ s` is pullback
along `s` followed by the pullback along the automorphism `σᵐ` of `Spec k̄`, which does not
change global sections. -/
noncomputable def stalkSheafFunctorSpecFrobeniusPowIso (m : ℕ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    stalkSheafFunctor k₀ l X ((specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) ≅
      stalkSheafFunctor k₀ l X s :=
  Functor.isoWhiskerRight (upperStarComp _ (specGeometricFrobenius k₀ ^ m).asIso.hom s) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (globalSectionsUpperStarIso _ (specGeometricFrobenius k₀ ^ m).asIso)

variable (k₀ l X) in
/-- The isomorphism `G_{s ≫ Frᵐ} ≅ ((Fr⁻ᵐ)_* G)_s` of stalk functors, from the composition of
pullbacks and `(Frᵐ)^* ≅ (Fr⁻ᵐ)_*`. -/
noncomputable def stalkSheafFunctorFrobeniusPowIso (m : ℕ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    stalkSheafFunctor k₀ l X (s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        m).asIso.hom) ≅
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_] ⋙
        stalkSheafFunctor k₀ l X s :=
  Functor.isoWhiskerRight (upperStarComp _ s
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv _
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso) _

variable (k₀ l X) in
/-- The isomorphism `G_s ≅ G_{σᵐ ≫ s} = G_{s ≫ Frᵐ} ≅ ((Fr⁻ᵐ)_* G)_s` of stalk functors at a
geometric point with `s ≫ Frᵐ = σᵐ ≫ s`. -/
noncomputable def stalkFrobeniusIso
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    stalkSheafFunctor k₀ l X s ≅
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_] ⋙
        stalkSheafFunctor k₀ l X s :=
  (stalkSheafFunctorSpecFrobeniusPowIso k₀ l X m s).symm ≪≫
    Functor.isoWhiskerRight (upperStarCongr _ hs.symm) _ ≪≫
    stalkSheafFunctorFrobeniusPowIso k₀ l X m s

section Monoidal

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ)

instance isMonoidal_stalkSheafFunctorSpecFrobeniusPowIso_hom :
    NatTrans.IsMonoidal (stalkSheafFunctorSpecFrobeniusPowIso k₀ l X m s).hom := by
  dsimp only [stalkSheafFunctorSpecFrobeniusPowIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

instance isMonoidal_stalkSheafFunctorFrobeniusPowIso_hom :
    NatTrans.IsMonoidal (stalkSheafFunctorFrobeniusPowIso k₀ l X m s).hom := by
  dsimp only [stalkSheafFunctorFrobeniusPowIso, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- The isomorphism `G_s ≅ ((Fr⁻ᵐ)_* G)_s` of stalk functors is monoidal. -/
instance isMonoidal_stalkFrobeniusIso_hom
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    NatTrans.IsMonoidal (stalkFrobeniusIso k₀ l X s m hs).hom := by
  dsimp only [stalkFrobeniusIso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]
  infer_instance

end Monoidal

section Frobenius

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)

lemma stalkObjSpecFrobeniusPowIso_eq (F : WeilSheaf k₀ l X) :
    F.stalkObjSpecFrobeniusPowIso m s =
      (stalkSheafFunctorSpecFrobeniusPowIso k₀ l X m s).app F.obj.carrier.X := by
  ext : 1
  simp [stalkObjSpecFrobeniusPowIso, stalkSheafFunctorSpecFrobeniusPowIso]

lemma stalkObjFrobeniusPowIso_eq (F : WeilSheaf k₀ l X) :
    F.stalkObjFrobeniusPowIso m s =
      (stalkSheafFunctorFrobeniusPowIso k₀ l X m s).app F.obj.carrier.X ≪≫
        (stalkSheafFunctor k₀ l X s).mapIso
          ((ProEtale.AdicSheaf.forget _).mapIso (F.frobeniusPowIso m)) := by
  ext : 1
  simp [stalkObjFrobeniusPowIso, stalkSheafFunctorFrobeniusPowIso]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private lemma isoWhiskerRight_upperStarCongr_app {t t' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (h : t = t')
    (G : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)) :
    (Functor.isoWhiskerRight (upperStarCongr (WeilCoefficients.{u} l) h)
        (Sheaf.Γ _ _)).app G =
      eqToIso (congrArg (fun t ↦ (stalkSheafFunctor k₀ l X t).obj G) h) := by
  subst h
  ext : 1
  simp [upperStarCongr]

private lemma stalkAt_frobenius_eq' (F : WeilSheaf k₀ l X) :
    (F.stalkAt s m hs).frobenius = WeilCoefficients.linearEquivOfIso
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s) :=
  rfl

/-- The Frobenius of the stalk of a Weil sheaf `F` at `s` is the isomorphism
`F_s ≅ ((Fr⁻ᵐ)_* F)_s` followed by the stalk of the iterated Weil structure `φ_m`. -/
theorem stalkAt_frobenius_eq_stalkFrobeniusIso (F : WeilSheaf k₀ l X) :
    (F.stalkAt s m hs).frobenius = WeilCoefficients.linearEquivOfIso
      ((stalkFrobeniusIso k₀ l X s m hs).app F.obj.carrier.X ≪≫
        (stalkSheafFunctor k₀ l X s).mapIso
          ((ProEtale.AdicSheaf.forget _).mapIso (F.frobeniusPowIso m))) := by
  rw [stalkAt_frobenius_eq', stalkObjSpecFrobeniusPowIso_eq, stalkObjFrobeniusPowIso_eq,
    stalkFrobeniusIso, NatIso.trans_app, NatIso.trans_app, isoWhiskerRight_upperStarCongr_app,
    Iso.trans_assoc, Iso.trans_assoc]
  rfl

variable {P Q R : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (WeilCoefficients.{u} l)}

omit [Fact (ringChar k₀ ≠ l)] in
/-- A pairing `e : P ⊗ Q ⟶ R` of sheaves compatible with isomorphisms `(Fr⁻ᵐ)_* P ≅ P`,
`(Fr⁻ᵐ)_* Q ≅ Q` and `(Fr⁻ᵐ)_* R ≅ R` induces a pairing of stalks compatible with the induced
automorphisms of the stalks. -/
theorem stalkPairing_frobenius
    (φP : (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_].obj P ⟶ P)
    (φQ : (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_].obj Q ⟶ Q)
    (φR : (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_].obj R ⟶ R)
    (e : P ⊗ Q ⟶ R)
    (h : (φP ⊗ₘ φQ) ≫ e = μ (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        m).asIso.inv)_*[WeilCoefficients.{u} l] P Q ≫
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_].map e ≫ φR) :
    (((stalkFrobeniusIso k₀ l X s m hs).hom.app P ≫ (stalkSheafFunctor k₀ l X s).map φP) ⊗ₘ
        ((stalkFrobeniusIso k₀ l X s m hs).hom.app Q ≫ (stalkSheafFunctor k₀ l X s).map φQ)) ≫
        μ (stalkSheafFunctor k₀ l X s) P Q ≫ (stalkSheafFunctor k₀ l X s).map e =
      (μ (stalkSheafFunctor k₀ l X s) P Q ≫ (stalkSheafFunctor k₀ l X s).map e) ≫
        (stalkFrobeniusIso k₀ l X s m hs).hom.app R ≫ (stalkSheafFunctor k₀ l X s).map φR := by
  rw [← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, ← Functor.map_comp, h,
    Functor.map_comp, Functor.map_comp, ← Category.assoc (μ _ _ _),
    ← Functor.LaxMonoidal.comp_μ, ← Category.assoc, ← Category.assoc,
    ← NatTrans.IsMonoidal.tensor (τ := (stalkFrobeniusIso k₀ l X s m hs).hom)]
  simp only [Category.assoc]
  rw [← Functor.comp_map, ← NatTrans.naturality_assoc]

omit [Fact (ringChar k₀ ≠ l)] in
/-- A unit `η : 𝟙 ⟶ R` compatible with an isomorphism `(Fr⁻ᵐ)_* R ≅ R` induces an element of
the stalk fixed by the induced automorphism of the stalk. -/
theorem stalkUnit_frobenius
    (φR : (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_].obj R ⟶ R)
    (η : 𝟙_ _ ⟶ R)
    (h : ε (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        m).asIso.inv)_*[WeilCoefficients.{u} l] ≫
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*[_].map η ≫
        φR = η) :
    (ε (stalkSheafFunctor k₀ l X s) ≫ (stalkSheafFunctor k₀ l X s).map η) ≫
        (stalkFrobeniusIso k₀ l X s m hs).hom.app R ≫ (stalkSheafFunctor k₀ l X s).map φR =
      ε (stalkSheafFunctor k₀ l X s) ≫ (stalkSheafFunctor k₀ l X s).map η := by
  rw [Category.assoc, NatTrans.naturality_assoc, ← Category.assoc (ε _),
    NatTrans.IsMonoidal.unit (τ := (stalkFrobeniusIso k₀ l X s m hs).hom)]
  conv_rhs => rw [← h]
  simp only [Functor.LaxMonoidal.comp_ε, Functor.comp_map, Functor.map_comp, Category.assoc]

end Frobenius

end AlgebraicGeometry.WeilSheaf
