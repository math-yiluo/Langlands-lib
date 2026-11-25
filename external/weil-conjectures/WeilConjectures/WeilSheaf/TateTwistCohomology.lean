/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.HomCoherence
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Cohomology of the Tate sheaves

The Tate sheaf `ℚ̄_ℓ(m)` is isomorphic, as a Weil sheaf, to the constant Weil twist of `ℚ̄_ℓ` by
`χ_ℓ(σ)^m = q^{-m}` (`AlgebraicGeometry.WeilSheaf.nonempty_tateTwistSheaf_iso_constantTwist`):
internal homs of constant twists of `ℚ̄_ℓ` are constant twists of `ℚ̄_ℓ`, the twists being
multiplicative in the first variable with exponent `-1` and in the second with exponent `1`.
Hence `Hʳ(X ⊗ k̄, ℚ̄_ℓ(m))` is `Hʳ(X ⊗ k̄, ℚ̄_ℓ)` with the geometric Frobenius multiplied by
`q^{-m}` (`AlgebraicGeometry.WeilSheaf.nonempty_equiv_cohomology_tateTwistSheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

lemma ihom_obj_str [Fact (ringChar k₀ ≠ l)] (A B : ProEtaleWeilSheaf k₀ l X) :
    (ihom k₀ l X A B).obj.str =
      (adicLowerStarCompIhomIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
          A.carrier).inv.app B.carrier ≫
        (Mod.ihomMap A.str.inv).app _ ≫ (AdicSheaf.ihom A.carrier).map B.obj.str :=
  rfl


variable [Fact (ringChar k₀ ≠ l)]

/-- `𝓗om(ℚ̄_ℓ, B) ≅ B` as pro-étale Weil sheaves. -/
noncomputable def ihomAdicConstantIso (B : ProEtaleWeilSheaf k₀ l X) :
    ihom k₀ l X (adicConstant k₀ l X) B ≅ B :=
  IsoAlgebra.isoMk (Mod.ihomRegularIso.app B.carrier) (by
    have h := map_ihomRegularIso_inv_app_comp_adicLowerStarCompIhomIso_inv_app l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm B.carrier
    have hs : (adicConstant k₀ l X).str =
        adicLowerStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm :=
      Iso.ext rfl
    have h' : (adicLowerStarCompIhomIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
          (adicConstant k₀ l X).carrier).inv.app B.carrier ≫
        (Mod.ihomMap (adicConstant k₀ l X).str.inv).app
          ((WeilSheaf.frobeniusPullback k₀ l X).obj B.carrier) =
        (WeilSheaf.frobeniusPullback k₀ l X).map (Mod.ihomRegularIso.hom.app B.carrier) ≫
          Mod.ihomRegularIso.inv.app ((WeilSheaf.frobeniusPullback k₀ l X).obj B.carrier) := by
      rw [← cancel_epi ((WeilSheaf.frobeniusPullback k₀ l X).map
        (Mod.ihomRegularIso.inv.app B.carrier)), ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp, hs]
      erw [reassoc_of% h]
      erw [← NatTrans.comp_app, ← Mod.ihomMap_comp, Iso.inv_hom_id, Mod.ihomMap_id,
        NatTrans.id_app, Category.comp_id]
      rfl
    rw [ihom_obj_str, Category.assoc, Category.assoc]
    erw [Mod.ihomRegularIso.hom.naturality B.obj.str]
    rw [reassoc_of% h']
    erw [Iso.inv_hom_id_app_assoc]
    rfl)


/-- An isomorphism `A ≅ A'` of pro-étale Weil sheaves induces `𝓗om(A', B) ≅ 𝓗om(A, B)`. -/
noncomputable def ihomMapIsoLeft {A A' : ProEtaleWeilSheaf k₀ l X} (φ : A ≅ A')
    (B : ProEtaleWeilSheaf k₀ l X) : ihom k₀ l X A' B ≅ ihom k₀ l X A B :=
  IsoAlgebra.isoMk ((Mod.ihomMapIso ((IsoAlgebra.forget _).mapIso φ)).app B.carrier) (by
    have h := adicLowerStarCompIhomIso_inv_app_comp_ihomMap l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv φ.hom.hom.f B.carrier
    have hφ : A.str.inv ≫ (WeilSheaf.frobeniusPullback k₀ l X).map φ.hom.hom.f =
        φ.hom.hom.f ≫ A'.str.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
      exact φ.hom.hom.h
    rw [ihom_obj_str, ihom_obj_str]
    change (WeilSheaf.frobeniusPullback k₀ l X).map ((Mod.ihomMap φ.hom.hom.f).app B.carrier) ≫ _ =
      _ ≫ (Mod.ihomMap φ.hom.hom.f).app B.carrier
    rw [← reassoc_of% h]
    simp only [Category.assoc]
    erw [(Mod.ihomMap φ.hom.hom.f).naturality B.obj.str]
    rw [← NatTrans.comp_app_assoc, ← NatTrans.comp_app_assoc, ← Mod.ihomMap_comp,
      ← Mod.ihomMap_comp, hφ])

/-- An isomorphism `B ≅ B'` of pro-étale Weil sheaves induces `𝓗om(A, B) ≅ 𝓗om(A, B')`. -/
noncomputable def ihomMapIsoRight (A : ProEtaleWeilSheaf k₀ l X) {B B' : ProEtaleWeilSheaf k₀ l X}
    (φ : B ≅ B') : ihom k₀ l X A B ≅ ihom k₀ l X A B' :=
  IsoAlgebra.isoMk ((AdicSheaf.ihom A.carrier).mapIso ((IsoAlgebra.forget _).mapIso φ))
    (ihom_map_comm A φ.hom)


omit [Fact (ringChar k₀ ≠ l)] in
lemma constantTwist_obj_obj_str (b : (PadicAlgCl l)ˣ) (K : ProEtaleWeilSheaf k₀ l X) :
    ((constantTwist k₀ l X b).obj K).obj.str =
      AdicSheaf.smul (ULift.up (b : PadicAlgCl l)) _ ≫ K.obj.str :=
  IsoAlgebra.twist_obj_obj_str _ _

omit [Fact (ringChar k₀ ≠ l)] in
lemma constantTwist_obj_str_inv (b : (PadicAlgCl l)ˣ) (K : ProEtaleWeilSheaf k₀ l X) :
    ((constantTwist k₀ l X b).obj K).str.inv =
      K.str.inv ≫ AdicSheaf.smul (ULift.up ((b⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) _ := by
  refine Iso.inv_ext ?_
  rw [IsoAlgebra.str_hom, constantTwist_obj_obj_str, Category.assoc, ← IsoAlgebra.str_hom,
    Iso.hom_inv_id_assoc]
  erw [AdicSheaf.smul_smul, ← AdicSheaf.smul_one]
  exact congrArg (AdicSheaf.smul · _) (congrArg ULift.up (by simp))

omit [Fact (ringChar k₀ ≠ l)] in
/-- Twisting by `b` and then by `c` is twisting by `b * c`. -/
noncomputable def constantTwistObjConstantTwistIso (b c : (PadicAlgCl l)ˣ)
    (K : ProEtaleWeilSheaf k₀ l X) :
    (constantTwist k₀ l X c).obj ((constantTwist k₀ l X b).obj K) ≅
      (constantTwist k₀ l X (b * c)).obj K :=
  IsoAlgebra.isoMk (Iso.refl _) (by
    simp only [constantTwist_obj_obj_str, Iso.refl_hom, Category.comp_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← Category.assoc]
    erw [AdicSheaf.smul_smul]
    exact congrArg (AdicSheaf.smul · _ ≫ _) (congrArg ULift.up (by simp)))


omit [Fact (ringChar k₀ ≠ l)] in
/-- Twisting by `1` does not change a pro-étale Weil sheaf. -/
noncomputable def constantTwistOneObjIso (K : ProEtaleWeilSheaf k₀ l X) :
    (constantTwist k₀ l X 1).obj K ≅ K :=
  IsoAlgebra.isoMk (Iso.refl _) (by
    simp only [constantTwist_obj_obj_str, Iso.refl_hom, Category.comp_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Units.val_one]
    erw [AdicSheaf.smul_one, Category.id_comp])

/-- `𝓗om(A ⊗ 𝓑_b, B) ≅ 𝓗om(A, B) ⊗ 𝓑_{b⁻¹}`, the identity on underlying sheaves. -/
noncomputable def ihomConstantTwistLeftIso (A B : ProEtaleWeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    ihom k₀ l X ((constantTwist k₀ l X b).obj A) B ≅
      (constantTwist k₀ l X b⁻¹).obj (ihom k₀ l X A B) :=
  IsoAlgebra.isoMk (K := ihom k₀ l X ((constantTwist k₀ l X b).obj A) B)
    (K' := (constantTwist k₀ l X b⁻¹).obj (ihom k₀ l X A B))
    (Iso.refl ((AdicSheaf.ihom A.carrier).obj B.carrier)) (by
      rw [constantTwist_obj_obj_str, ihom_obj_str, ihom_obj_str, constantTwist_obj_str_inv]
      simp only [Iso.refl_hom, Mod.ihomMap_comp, NatTrans.comp_app, AdicSheaf.ihomMap_smul_app]
      change (WeilSheaf.frobeniusPullback k₀ l X).map (𝟙 _) ≫
          AdicSheaf.smul _ ((WeilSheaf.frobeniusPullback k₀ l X).obj
            ((AdicSheaf.ihom A.carrier).obj B.carrier)) ≫ _ =
        _ ≫ 𝟙 ((AdicSheaf.ihom A.carrier).obj B.carrier)
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
        reassoc_of% (AdicSheaf.smul_comp _ ((adicLowerStarCompIhomIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv A.carrier).inv.app
            B.carrier))]
      simp only [Category.assoc]
      rfl)

/-- `𝓗om(A, B ⊗ 𝓑_c) ≅ 𝓗om(A, B) ⊗ 𝓑_c`, the identity on underlying sheaves. -/
noncomputable def ihomConstantTwistRightIso (A B : ProEtaleWeilSheaf k₀ l X) (c : (PadicAlgCl l)ˣ) :
    ihom k₀ l X A ((constantTwist k₀ l X c).obj B) ≅
      (constantTwist k₀ l X c).obj (ihom k₀ l X A B) :=
  IsoAlgebra.isoMk (K := ihom k₀ l X A ((constantTwist k₀ l X c).obj B))
    (K' := (constantTwist k₀ l X c).obj (ihom k₀ l X A B))
    (Iso.refl ((AdicSheaf.ihom A.carrier).obj B.carrier)) (by
      rw [constantTwist_obj_obj_str, ihom_obj_str, ihom_obj_str, constantTwist_obj_obj_str]
      change (WeilSheaf.frobeniusPullback k₀ l X).map (𝟙 _) ≫
          AdicSheaf.smul _ ((WeilSheaf.frobeniusPullback k₀ l X).obj
            ((AdicSheaf.ihom A.carrier).obj B.carrier)) ≫ _ =
        _ ≫ 𝟙 ((AdicSheaf.ihom A.carrier).obj B.carrier)
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
        reassoc_of% (AdicSheaf.smul_comp _ ((adicLowerStarCompIhomIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv A.carrier).inv.app
            B.carrier)),
        reassoc_of% (AdicSheaf.smul_comp _ ((Mod.ihomMap A.str.inv).app
          ((WeilSheaf.frobeniusPullback k₀ l X).obj B.carrier))), Functor.map_comp]
      erw [AdicSheaf.ihom_map_smul]
      rfl)

omit [Fact (ringChar k₀ ≠ l)] in
/-- Constant twists by equal units are isomorphic. -/
noncomputable def constantTwistCongrIso {b c : (PadicAlgCl l)ˣ} (h : b = c)
    (K : ProEtaleWeilSheaf k₀ l X) :
    (constantTwist k₀ l X b).obj K ≅ (constantTwist k₀ l X c).obj K :=
  eqToIso (by rw [h])

/-- `𝓗om(ℚ̄_ℓ ⊗ 𝓑_b, ℚ̄_ℓ ⊗ 𝓑_c) ≅ ℚ̄_ℓ ⊗ 𝓑_{b⁻¹ c}` as pro-étale Weil sheaves. -/
noncomputable def ihomConstantTwistAdicConstantIso (b c : (PadicAlgCl l)ˣ) :
    ihom k₀ l X ((constantTwist k₀ l X b).obj (adicConstant k₀ l X))
        ((constantTwist k₀ l X c).obj (adicConstant k₀ l X)) ≅
      (constantTwist k₀ l X (b⁻¹ * c)).obj (adicConstant k₀ l X) :=
  ihomConstantTwistLeftIso _ _ b ≪≫
    (constantTwist k₀ l X b⁻¹).mapIso (ihomConstantTwistRightIso _ _ c ≪≫
      (constantTwist k₀ l X c).mapIso (ihomAdicConstantIso _)) ≪≫
    constantTwistObjConstantTwistIso c b⁻¹ _ ≪≫ constantTwistCongrIso (mul_comm _ _) _

end ProEtaleWeilSheaf

namespace WeilSheaf

open ProEtaleWeilSheaf

variable [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The dual of a Weil sheaf whose underlying pro-étale Weil sheaf is `ℚ̄_ℓ ⊗ 𝓑_b` is
`ℚ̄_ℓ ⊗ 𝓑_{b⁻¹}`. -/
noncomputable def dualObjIsoOfIso (F : WeilSheaf k₀ l X) (hF : F.IsLisse) {b : (PadicAlgCl l)ˣ}
    (e : F.obj ≅ (ProEtaleWeilSheaf.constantTwist k₀ l X b).obj
      (ProEtaleWeilSheaf.adicConstant k₀ l X)) :
    (F.dual hF).obj ≅ (ProEtaleWeilSheaf.constantTwist k₀ l X b⁻¹).obj
      (ProEtaleWeilSheaf.adicConstant k₀ l X) :=
  ihomMapIsoLeft e.symm _ ≪≫ ihomMapIsoRight _ (constantTwistOneObjIso _).symm ≪≫
    ihomConstantTwistAdicConstantIso b 1 ≪≫ constantTwistCongrIso (mul_one _) _

/-- The tensor product of Weil sheaves whose underlying pro-étale Weil sheaves are `ℚ̄_ℓ ⊗ 𝓑_b`
and `ℚ̄_ℓ ⊗ 𝓑_c` is `ℚ̄_ℓ ⊗ 𝓑_{b c}`. -/
noncomputable def tensorObjObjIsoOfIso (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    {b c : (PadicAlgCl l)ˣ}
    (e : F.obj ≅ (ProEtaleWeilSheaf.constantTwist k₀ l X b).obj
      (ProEtaleWeilSheaf.adicConstant k₀ l X))
    (e' : G.obj ≅ (ProEtaleWeilSheaf.constantTwist k₀ l X c).obj
      (ProEtaleWeilSheaf.adicConstant k₀ l X)) :
    (F.tensorObj G hF).obj ≅ (ProEtaleWeilSheaf.constantTwist k₀ l X (b * c)).obj
      (ProEtaleWeilSheaf.adicConstant k₀ l X) :=
  ihomMapIsoLeft (dualObjIsoOfIso F hF e).symm _ ≪≫ ihomMapIsoRight _ e' ≪≫
    ihomConstantTwistAdicConstantIso b⁻¹ c ≪≫ constantTwistCongrIso (by rw [inv_inv]) _

variable (k₀ l X)

/-- The non-negative Tate sheaf `ℚ̄_ℓ(n)` is `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ⁿ}`. -/
noncomputable def tateTwistSheafNatObjIso : ∀ n : ℕ, (tateTwistSheafNat k₀ l X n).obj ≅
    (ProEtaleWeilSheaf.constantTwist k₀ l X (cyclotomicUnit k₀ l ^ n)).obj
      (ProEtaleWeilSheaf.adicConstant k₀ l X)
  | 0 => (constantTwistOneObjIso _).symm ≪≫ constantTwistCongrIso (pow_zero _).symm _
  | 1 => (adicConstant k₀ l X).constantTwistObjIso (cyclotomicUnit k₀ l) ≪≫
      constantTwistCongrIso (pow_one _).symm _
  | n + 2 => tensorObjObjIsoOfIso _ _ _
      ((adicConstant k₀ l X).constantTwistObjIso (cyclotomicUnit k₀ l))
      (tateTwistSheafNatObjIso (n + 1)) ≪≫ constantTwistCongrIso (pow_succ' _ _).symm _

/-- The Tate sheaf `ℚ̄_ℓ(m)` is `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ}`. -/
noncomputable def tateTwistSheafObjIso : ∀ m : ℤ, (tateTwistSheaf k₀ l X m).obj ≅
    (ProEtaleWeilSheaf.constantTwist k₀ l X (cyclotomicUnit k₀ l ^ m)).obj
      (ProEtaleWeilSheaf.adicConstant k₀ l X)
  | (n : ℕ) => tateTwistSheafNatObjIso k₀ l X n ≪≫
      constantTwistCongrIso (zpow_natCast _ _).symm _
  | .negSucc n => dualObjIsoOfIso _ (isLisse_tateTwistSheafNat k₀ l X _)
      (tateTwistSheafNatObjIso k₀ l X (n + 1)) ≪≫
      constantTwistCongrIso (zpow_negSucc _ _).symm _

/-- **The Tate sheaves are constant twists** (compatibility of the Tate twists). The Tate sheaf
`ℚ̄_ℓ(m)` is isomorphic, as a Weil sheaf, to the constant Weil twist `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ}` of
`ℚ̄_ℓ`: the Weil structure of `ℚ̄_ℓ(1)`, the pullback of roots of unity, is `χ_ℓ(σ)` times that of
`ℚ̄_ℓ`, and the tensor products and duals defining `ℚ̄_ℓ(m)` give `χ_ℓ(σ)ᵐ`.
(blueprint: `proposition-weights-under-usual-operations--13`) -/
noncomputable def tateTwistSheafIso (m : ℤ) :
    tateTwistSheaf k₀ l X m ≅ (adicConstant k₀ l X).constantTwist (cyclotomicUnit k₀ l ^ m) :=
  ObjectProperty.isoMk _
    (tateTwistSheafObjIso k₀ l X m ≪≫ ((adicConstant k₀ l X).constantTwistObjIso _).symm)

variable {k₀ l X}

/-- The value `χ_ℓ(σ)ᵐ = q⁻ᵐ` of the cyclotomic unit. -/
lemma cyclotomicUnit_zpow_eq (m : ℤ) :
    ((cyclotomicUnit k₀ l ^ m : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      (Nat.card k₀ : PadicAlgCl l) ^ (-m) := by
  rw [Units.val_zpow_eq_zpow_val, cyclotomicUnit_eq, inv_zpow', zpow_neg]

section Cohomology

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- Isomorphic Weil sheaves have isomorphic cohomology, with its Frobenius. -/
noncomputable def cohomologyEquivOfIso {F G : WeilSheaf k₀ l Y} (e : F ≅ G) (r : ℤ) :
    (F.cohomology r).Equiv (G.cohomology r) :=
  globalSectionsEquivOfIso ((WeilComplex.homologySheaf r).mapIso
    ((WeilComplex.derivedLowerStar (Y ↘ Spec (CommRingCat.of k₀))).mapIso (toComplex.mapIso e)))

variable (k₀ l Y) in
/-- **Cohomology of the Tate sheaves** (blueprint `prose-10-21`, with
the twist elimination of `corollary-degreewise-duality-over-fields--1`): `Hʳ(Y ⊗ k̄, ℚ̄_ℓ(m))` is
`Hʳ(Y ⊗ k̄, ℚ̄_ℓ)(m)`, the same space with the geometric Frobenius multiplied by `q^{-m}`, since
geometric Frobenius acts on `ℚ̄_ℓ(m)` by `q^{-m}`. -/
theorem nonempty_equiv_cohomology_tateTwistSheaf (m r : ℤ) :
    Nonempty (((tateTwistSheaf k₀ l Y m).cohomology r).Equiv
      (((adicConstant k₀ l Y).cohomology r).tateTwist (Nat.card k₀) m)) := by
  obtain ⟨E⟩ := nonempty_equiv_cohomology_constantTwist (adicConstant k₀ l Y)
    (cyclotomicUnit k₀ l ^ m) r
  unfold FrobeniusModule.tateTwist
  rw [← cyclotomicUnit_zpow_eq]
  exact ⟨(cohomologyEquivOfIso (tateTwistSheafIso k₀ l Y m) r).trans E⟩

end Cohomology


section CompactSupport

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- Isomorphic Weil sheaves have isomorphic compactly supported cohomology, with its
Frobenius. -/
noncomputable def compactlySupportedCohomologyEquivOfIso {F G : WeilSheaf k₀ l Y} (e : F ≅ G)
    (r : ℤ) : (F.compactlySupportedCohomology r).Equiv (G.compactlySupportedCohomology r) :=
  globalSectionsEquivOfIso ((WeilComplex.homologySheaf r).mapIso
    ((WeilComplex.derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))).mapIso
      (toComplex.mapIso e)))

variable (k₀ l Y) in
/-- **Compactly supported cohomology of the Tate sheaves** (blueprint
`prose-10-21`, with the twist elimination of
`corollary-degreewise-duality-over-fields--1`): `H_cʳ(Y ⊗ k̄, ℚ̄_ℓ(m))` is `H_cʳ(Y ⊗ k̄, ℚ̄_ℓ)(m)`,
the same space with the geometric Frobenius multiplied by `q^{-m}`. -/
theorem nonempty_equiv_compactlySupportedCohomology_tateTwistSheaf (m r : ℤ) :
    Nonempty (((tateTwistSheaf k₀ l Y m).compactlySupportedCohomology r).Equiv
      (((adicConstant k₀ l Y).compactlySupportedCohomology r).tateTwist (Nat.card k₀) m)) := by
  obtain ⟨E⟩ := nonempty_equiv_compactlySupportedCohomology_constantTwist (adicConstant k₀ l Y)
    (cyclotomicUnit k₀ l ^ m) r
  unfold FrobeniusModule.tateTwist
  rw [← cyclotomicUnit_zpow_eq]
  exact ⟨(compactlySupportedCohomologyEquivOfIso (tateTwistSheafIso k₀ l Y m) r).trans E⟩

end CompactSupport
end WeilSheaf

end AlgebraicGeometry
