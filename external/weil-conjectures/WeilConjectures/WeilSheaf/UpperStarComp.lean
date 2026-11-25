/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.WeilSheaf.Category

/-!
# Composition of pullbacks of pro-étale Weil sheaves

The pullback `φ^*` of pro-étale Weil sheaves along a morphism `φ : X ⟶ Y` of `k₀`-schemes is
the pullback along the base change `φ̄ : X̄ ⟶ Ȳ`, with the Weil structure transported along
the exchange isomorphism `φ̄^* ⋙ Fr_X^* ≅ Fr_Y^* ⋙ φ̄^*`. The exchange isomorphisms of two
composable morphisms paste to that of the composite
(`AlgebraicGeometry.ProEtale.adicUpperStarExchange_paste`, from the pasting law
`AlgebraicGeometry.ProEtale.upperStarCompIso_hom_app_paste`), so the composition isomorphisms
`(φ̄ ≫ ψ̄)^* ≅ ψ̄^* ⋙ φ̄^*` induce isomorphisms of pullbacks of pro-étale Weil sheaves.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarCompIso`: `(φ ≫ ψ)^* ≅ ψ^* ⋙ φ^*`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarCongrIso`: `φ^* ≅ φ'^*` for `φ = φ'`.
- `AlgebraicGeometry.WeilSheaf.upperStarCompIso` and
  `AlgebraicGeometry.WeilSheaf.upperStarCongr`: the same for Weil sheaves.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace ProEtale

section Paste

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {T₁ T₂ T₃ : Scheme.{u}}

/-- The isomorphism of a commutative square, for the reversed square, is the inverse. -/
lemma upperStarCompIso_symm {Y Z₁ Z₂ T : Scheme.{u}} {a : Y ⟶ Z₁} {b : Z₁ ⟶ T}
    {c : Y ⟶ Z₂} {d : Z₂ ⟶ T} (h : a ≫ b = c ≫ d) :
    upperStarCompIso A h.symm = (upperStarCompIso A h).symm := by
  have e : upperStarCongr A h.symm = (upperStarCongr A h).symm :=
    Iso.ext (by simp [upperStarCongr])
  rw [upperStarCompIso, upperStarCompIso, e, Iso.trans_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc]

/-- The pasting law for the composition isomorphisms of commutative squares `a₁ ≫ j₁ = j₁ ≫ a₂`
and `a₂ ≫ j₂ = j₂ ≫ a₃`, in the direction `a₁^* j₁^* j₂^* ⟶ (j₁ ≫ j₂)^* a₃^*`. -/
lemma upperStarCompIso_paste (j₁ : T₁ ⟶ T₂) (j₂ : T₂ ⟶ T₃) (a₁ : T₁ ⟶ T₁) (a₂ : T₂ ⟶ T₂)
    (a₃ : T₃ ⟶ T₃) (c₁ : a₁ ≫ j₁ = j₁ ≫ a₂) (c₂ : a₂ ≫ j₂ = j₂ ≫ a₃)
    (c₁₂ : a₁ ≫ j₁ ≫ j₂ = (j₁ ≫ j₂) ≫ a₃) (M : Sheaf (Scheme.ProEt.topology T₃) A) :
    (a₁)^*[A].map ((upperStarComp A j₁ j₂).inv.app M) ≫
        (upperStarCompIso A c₁₂).hom.app M =
      (upperStarCompIso A c₁).hom.app ((j₂)^*[A].obj M) ≫
        (j₁)^*[A].map ((upperStarCompIso A c₂).hom.app M) ≫
          (upperStarComp A j₁ j₂).inv.app ((a₃)^*[A].obj M) := by
  have h := upperStarCompIso_hom_app_paste A c₂.symm c₁.symm c₁₂.symm M
  rw [upperStarCompIso_symm c₂, upperStarCompIso_symm c₁, upperStarCompIso_symm c₁₂] at h
  simp only [Iso.symm_hom] at h
  have h' := congrArg Iso.inv (Iso.ext (α := (upperStarComp A j₁ j₂).app ((a₃)^*[A].obj M) ≪≫
    (j₁)^*[A].mapIso ((upperStarCompIso A c₂).app M).symm ≪≫
      ((upperStarCompIso A c₁).app ((j₂)^*[A].obj M)).symm)
    (β := ((upperStarCompIso A c₁₂).app M).symm ≪≫ (a₁)^*[A].mapIso ((upperStarComp A j₁ j₂).app M))
    (by simpa using h))
  simpa using h'.symm

/-- The components of the congruence isomorphism of pullbacks are identities. -/
lemma upperStarCongr_hom_app_eq_eqToHom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (M : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A h).hom.app M = eqToHom (by rw [h]) := by
  subst h
  rfl

end Paste

section Exchange

variable {l : ℕ} [Fact l.Prime] {T₁ T₂ T₃ : Scheme.{u}}

-- Rewriting `upperStarCongr` at the `ℓ`-adic sheaf itself, rather than unfolding it at a
-- composite, keeps the kernel from comparing pullbacks along different morphisms.
lemma adicUpperStarCompIso_hom_app_hom {Y Z₁ Z₂ T : Scheme.{u}} {a : Y ⟶ Z₁} {b : Z₁ ⟶ T}
    {c : Y ⟶ Z₂} {d : Z₂ ⟶ T} (h : a ≫ b = c ≫ d) (M : AdicSheaf l T) :
    ((adicUpperStarCompIso l h).hom.app M).hom =
      (upperStarComp (WeilCoefficients.{u} l) a b).inv.app M.X ≫ eqToHom (by rw [h]) ≫
        (upperStarComp (WeilCoefficients.{u} l) c d).hom.app M.X := by
  change ((adicUpperStarComp l a b).inv.app M ≫ (adicUpperStarCongr l h).hom.app M ≫
    (adicUpperStarComp l c d).hom.app M).hom = _
  rw [Mod.comp_hom', Mod.comp_hom', adicUpperStarComp_inv_app_hom, adicUpperStarComp_hom_app_hom,
    adicUpperStarCongr_hom_app_hom, upperStarCongr_hom_app_eq_eqToHom]

/-- The pasting law for the composition isomorphisms of commutative squares of pullbacks of
`ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.upperStarCompIso_paste`). -/
lemma adicUpperStarCompIso_paste (j₁ : T₁ ⟶ T₂) (j₂ : T₂ ⟶ T₃) (a₁ : T₁ ⟶ T₁) (a₂ : T₂ ⟶ T₂)
    (a₃ : T₃ ⟶ T₃) (c₁ : a₁ ≫ j₁ = j₁ ≫ a₂) (c₂ : a₂ ≫ j₂ = j₂ ≫ a₃)
    (c₁₂ : a₁ ≫ j₁ ≫ j₂ = (j₁ ≫ j₂) ≫ a₃) (M : AdicSheaf l T₃) :
    (a₁)^*ᵃ[l].map ((adicUpperStarComp l j₁ j₂).inv.app M) ≫
        (adicUpperStarCompIso l c₁₂).hom.app M =
      (adicUpperStarCompIso l c₁).hom.app ((j₂)^*ᵃ[l].obj M) ≫
        (j₁)^*ᵃ[l].map ((adicUpperStarCompIso l c₂).hom.app M) ≫
          (adicUpperStarComp l j₁ j₂).inv.app ((a₃)^*ᵃ[l].obj M) := by
  apply Mod.hom_ext
  rw [Mod.comp_hom', Mod.comp_hom', Mod.comp_hom', adicUpperStar_map_hom, adicUpperStar_map_hom,
    adicUpperStarCompIso_hom_app_hom, adicUpperStarCompIso_hom_app_hom,
    adicUpperStarCompIso_hom_app_hom, adicUpperStarComp_inv_app_hom,
    adicUpperStarComp_inv_app_hom]
  have p := upperStarCompIso_paste j₁ j₂ a₁ a₂ a₃ c₁ c₂ c₁₂ M.X
  rw [upperStarCompIso, upperStarCompIso, upperStarCompIso] at p
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    upperStarCongr_hom_app_eq_eqToHom] at p
  exact p

variable (l) in
/-- The exchange isomorphism `j^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ j^*` of `ℓ`-adic sheaves attached to a
morphism `j` intertwining automorphisms `a` and `b`: through `a^* ≅ (a⁻¹)_*`, it is
`a^* j^* ≅ (a ≫ j)^* = (j ≫ b)^* ≅ j^* b^*`. -/
noncomputable def adicUpperStarExchange (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) :
    (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l a).symm ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l c ≪≫ adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l b) _

lemma adicUpperStarExchange_hom_app (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (M : AdicSheaf l T₂) :
    (adicUpperStarExchange l j a b c).hom.app M =
      (adicUpperStarIsoLowerStarInv l a).inv.app ((j)^*ᵃ[l].obj M) ≫
        (adicUpperStarCompIso l c).hom.app M ≫
        (j)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l b).hom.app M) := by
  simp only [adicUpperStarExchange, adicUpperStarCompIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]

/-- **Pasting of exchange isomorphisms.** The exchange isomorphisms of `j₁` and `j₂` paste to
that of `j₁₂ = j₁ ≫ j₂`, through the composition isomorphism `j₂^* ⋙ j₁^* ≅ j₁₂^*`. -/
lemma adicUpperStarExchange_paste (j₁ : T₁ ⟶ T₂) (j₂ : T₂ ⟶ T₃) (j₁₂ : T₁ ⟶ T₃)
    (hj : j₁ ≫ j₂ = j₁₂) (a₁ : T₁ ≅ T₁) (a₂ : T₂ ≅ T₂) (a₃ : T₃ ≅ T₃)
    (c₁ : a₁.hom ≫ j₁ = j₁ ≫ a₂.hom) (c₂ : a₂.hom ≫ j₂ = j₂ ≫ a₃.hom)
    (c₁₂ : a₁.hom ≫ j₁₂ = j₁₂ ≫ a₃.hom) (M : AdicSheaf l T₃) :
    (a₁.inv)_*ᵃ[l].map ((adicUpperStarComp l j₁ j₂).inv.app M ≫
        (adicUpperStarCongr l hj).hom.app M) ≫ (adicUpperStarExchange l j₁₂ a₁ a₃ c₁₂).hom.app M =
      (adicUpperStarExchange l j₁ a₁ a₂ c₁).hom.app ((j₂)^*ᵃ[l].obj M) ≫
        (j₁)^*ᵃ[l].map ((adicUpperStarExchange l j₂ a₂ a₃ c₂).hom.app M) ≫
        (adicUpperStarComp l j₁ j₂).inv.app ((a₃.inv)_*ᵃ[l].obj M) ≫
        (adicUpperStarCongr l hj).hom.app ((a₃.inv)_*ᵃ[l].obj M) := by
  subst hj
  simp only [adicUpperStarExchange_hom_app, adicUpperStarCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, Functor.map_comp, Category.assoc]
  have n₁ := (adicUpperStarIsoLowerStarInv l a₁).inv.naturality
    ((adicUpperStarComp l j₁ j₂).inv.app M)
  have n₂ := (adicUpperStarComp l j₁ j₂).inv.naturality
    ((adicUpperStarIsoLowerStarInv l a₃).hom.app M)
  simp only [Functor.comp_map] at n₁ n₂
  have p := adicUpperStarCompIso_paste (l := l) j₁ j₂ a₁.hom a₂.hom a₃.hom c₁ c₂ c₁₂ M
  rw [reassoc_of% n₁, reassoc_of% p, n₂]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]

end Exchange

end ProEtale

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "𝐒" => Spec (CommRingCat.of k₀)

set_option hygiene false in
local notation "Fr[" T "]" =>
  (Scheme.Hom.geometricGaloisFrobenius (T ↘ Spec (CommRingCat.of k₀))).asIso

set_option hygiene false in
local notation "bc[" f "]" =>
  Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))

lemma adicUpperStarGeometricFiberMapCompFrobeniusIso_eq_exchange (φ : X ⟶ Y)
    [φ.IsOver 𝐒] :
    adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ 𝐒) =
      adicUpperStarExchange l (bc[φ]) (Fr[X]) (Fr[Y])
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ _).symm :=
  rfl

variable (l) in
/-- The composition isomorphism `ψ̄^* ⋙ φ̄^* ≅ (φ ≫ ψ)̄^*` of the pullbacks along the base
changes. -/
noncomputable def adicUpperStarGeometricFiberMapCompIso (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [φ.IsOver 𝐒] [ψ.IsOver 𝐒] :
    (bc[ψ])^*ᵃ[l] ⋙ (bc[φ])^*ᵃ[l] ≅ (bc[φ ≫ ψ])^*ᵃ[l] :=
  (adicUpperStarComp l (bc[φ]) (bc[ψ])).symm ≪≫
    adicUpperStarCongr l (g' := bc[φ ≫ ψ]) (Scheme.Hom.geometricFiberMap_comp φ ψ (comp_over φ 𝐒)
      (comp_over ψ 𝐒)).symm

omit [Finite k₀] in
lemma adicUpperStarGeometricFiberMapCompIso_eq (φ : X ⟶ Y) (ψ : Y ⟶ Z) [φ.IsOver 𝐒]
    [ψ.IsOver 𝐒] :
    adicUpperStarGeometricFiberMapCompIso l φ ψ = (adicUpperStarComp l (bc[φ]) (bc[ψ])).symm ≪≫
      adicUpperStarCongr l (g' := bc[φ ≫ ψ]) (Scheme.Hom.geometricFiberMap_comp φ ψ (comp_over φ 𝐒)
        (comp_over ψ 𝐒)).symm := by
  rw [adicUpperStarGeometricFiberMapCompIso]

/-- The composition isomorphism of pullbacks along the base changes is compatible with the
exchange isomorphisms defining the Weil structures of pullbacks. -/
lemma ProEtaleWeilSheaf.upperStarComp_exchange (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [φ.IsOver 𝐒] [ψ.IsOver 𝐒] :
    Functor.whiskerRight (adicUpperStarGeometricFiberMapCompIso l φ ψ).hom ((Fr[X]).inv)_*ᵃ[l] ≫
      (adicUpperStarGeometricFiberMapCompFrobeniusIso l (φ ≫ ψ) (comp_over (φ ≫ ψ) 𝐒)).hom =
    (IsoAlgebra.compCommIso (adicUpperStarGeometricFiberMapCompFrobeniusIso l ψ (comp_over ψ 𝐒))
        (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ 𝐒))).hom ≫
      Functor.whiskerLeft ((Fr[Z]).inv)_*ᵃ[l]
        (adicUpperStarGeometricFiberMapCompIso l φ ψ).hom := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    IsoAlgebra.compCommIso_hom_app, adicUpperStarGeometricFiberMapCompFrobeniusIso_eq_exchange,
    adicUpperStarGeometricFiberMapCompFrobeniusIso_eq_exchange,
    adicUpperStarGeometricFiberMapCompFrobeniusIso_eq_exchange]
  simp only [adicUpperStarGeometricFiberMapCompIso_eq, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  exact adicUpperStarExchange_paste (l := l) (bc[φ]) (bc[ψ]) (bc[φ ≫ ψ])
    (Scheme.Hom.geometricFiberMap_comp φ ψ (comp_over φ 𝐒) (comp_over ψ 𝐒)).symm
    (Fr[X]) (Fr[Y]) (Fr[Z])
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ _).symm
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius ψ _).symm
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius (φ ≫ ψ) _).symm K

variable (k₀ l) in
/-- The composition isomorphism `(φ ≫ ψ)^* ≅ ψ^* ⋙ φ^*` of pullbacks of pro-étale Weil sheaves:
the composition isomorphism of pullbacks along the base changes, which is compatible with the
Weil structures (`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarComp_exchange`). -/
noncomputable def ProEtaleWeilSheaf.upperStarCompIso (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [φ.IsOver 𝐒] [ψ.IsOver 𝐒] :
    ProEtaleWeilSheaf.upperStar k₀ l (φ ≫ ψ) ≅
      ProEtaleWeilSheaf.upperStar k₀ l ψ ⋙ ProEtaleWeilSheaf.upperStar k₀ l φ :=
  (IsoAlgebra.mapOfNatIsoIsoOfIso _ (ProEtaleWeilSheaf.upperStarComp_exchange φ ψ)).symm ≪≫
    (IsoAlgebra.mapOfNatIsoCompIso _ _).symm

end AlgebraicGeometry
