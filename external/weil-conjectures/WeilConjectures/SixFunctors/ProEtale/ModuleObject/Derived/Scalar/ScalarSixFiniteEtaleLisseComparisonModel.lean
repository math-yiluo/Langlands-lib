/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
import WeilConjectures.CategoryTheory.ModuleObjects.MapModFiniteFree
import WeilConjectures.Mathlib.CategoryTheory.Retract
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.FiniteComparisonConstantRealization
import all WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel

/-! # Scalar models of finite projective constant modules

Source: blueprint scalar-six-ctf (1), finite projective local models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The scalar of `Λ(*)` given by the sections at the point of a condensed scalar `b` is
sent back to `b` by `pointScalarSection`. -/
private theorem pointScalarSection_sections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (b : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ) :
    pointScalarSection Λ
      (Functor.LaxMonoidal.ε scalarSections.{u} ≫ scalarSections.{u}.map b) = b := by
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let G := (sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
    (Opposite.op (Profinite.of PUnit.{u + 1}))
  let : G.LaxMonoidal := scalarSections_laxMonoidal
  let adj : F ⊣ G := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  have : adj.IsMonoidal := inferInstance
  have h := adj.counit_naturality b
  have hε := adj.map_ε_comp_counit_app_unit
  dsimp only [pointScalarSection]
  rw [Functor.map_comp, Category.assoc]
  erw [h, reassoc_of% hε]
  rw [← Category.assoc, Functor.Monoidal.ε_η, Category.id_comp]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

omit [DiscreteTopology A] [Finite A] in
/-- The specified finite comparison of a constant finite projective module is the
finite scalar extension of a retract of a finite free scalar module.

Source: blueprint scalar-six-ctf (1), finite ring generators; Stacks 00NX and 099Y.

Proof: split a finite free surjection onto P using projectivity. The constant condensed
model on the point is additive and sends the free module of rank n to the free condensed
module, so the model of P is a retract of a free condensed module. Its idempotent has
entries in Λ(*), and sections at the point give a retract Q of the free scalar module with
the same scalar entries. The realization of the constant sheaf on P is pulled back from the
point model, so both it and the scalar extension of Q are retracts of the free module on T
for the same scalar matrix, hence isomorphic. This includes the zero ring, rank zero and
the empty scheme. -/
theorem finiteProjectiveConstantScalarModel
    (T : Scheme.{u})
    (P : ModuleCat.{u + 1} (ULift.{u + 1} A))
    (hfin : Module.Finite (ULift.{u + 1} A) P)
    (hproj : Module.Projective (ULift.{u + 1} A) P) :
    ∃ (Q : Mod Ab.{u + 1} (scalarRingObj Λ.X)) (n : ℕ),
      Nonempty (Retract Q (Mod.finiteFree (scalarRingObj Λ.X) n)) ∧
      Nonempty ((Mod.comap (coefficientMap e.hom.hom T)).obj
        ((finiteComparisonRealization A T eR).obj
          ((constantSheaf (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P)) ≅
        (finiteConstantScalarExtension Λ.X T).obj Q) := by
  classical
  let R := ULift.{u + 1} A
  -- P is a retract of a finite free module.
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  let ρ : Retract P (ModuleCat.of R (Fin n → R)) :=
    { i := ModuleCat.ofHom g
      r := ModuleCat.ofHom f
      retract := by
        ext x
        exact LinearMap.congr_fun hg x }
  -- The condensed point model of P is a retract of a free condensed module.
  let a := e.hom.hom
  have : IsIso a := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  let Mc := Mod.comap (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) a
  let : Mc.IsEquivalence := (Mod.comapEquivalenceOfIsIso a).isEquivalence_functor
  let : Mc.Additive := Functor.additive_of_preserves_binary_products _
  let freeC : Mc.obj (Mod.finiteFree _ n) ≅ Mod.finiteFree Λ.X n :=
    Mc.mapBiproduct (fun _ : Fin n ↦ Mod.regular _) ≪≫
      biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv a))
  let M := pointConstantModule A eR ⋙ Mc
  let ρ₁ : Retract (M.obj P) (Mod.finiteFree Λ.X n) :=
    (ρ.map M).trans
      (Retract.ofIso (Mc.mapIso (pointConstantModuleFiniteFreeIso A eR n) ≪≫ freeC))
  let p := ρ₁.r ≫ ρ₁.i
  -- The scalar entries of its idempotent.
  let b (j k : Fin n) : 𝟙_ _ ⟶ Λ.X :=
    (MonObj.one : 𝟙_ _ ⟶ Λ.X) ≫ (biproduct.ι _ j ≫ p ≫ biproduct.π _ k).hom
  let c (j k : Fin n) : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ.X :=
    Functor.LaxMonoidal.ε scalarSections.{u} ≫ scalarSections.{u}.map (b j k)
  have hb : (biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular Λ.X) (b j k)) = p :=
    pointMatrix_reconstruct Λ.X p
  have hc (j k : Fin n) : pointScalarSection Λ.X (c j k) = b j k :=
    pointScalarSection_sections Λ.X (b j k)
  have hp : p = biproduct.matrix fun j k ↦
      Mod.regularLift (Mod.regular Λ.X) (pointScalarSection Λ.X (c j k)) := by
    simp only [hc]
    exact hb.symm
  -- Sections at the point give the scalar retract Q.
  have : PreservesLimitsOfSize.{0, 0} scalarSections.{u} :=
    (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).rightAdjoint_preservesLimits
  have : scalarSections.{u}.Additive := Functor.additive_of_preserves_binary_products _
  let Γ := scalarSections.{u}.mapMod Λ.X
  let ρQ : Retract (Γ.obj (M.obj P)) (Mod.finiteFree (scalarRingObj Λ.X) n) :=
    (ρ₁.map Γ).trans (Retract.ofIso (scalarSections.{u}.mapModFiniteFreeIso Λ.X n))
  have hq : ρQ.r ≫ ρQ.i = biproduct.matrix fun j k ↦
      Mod.regularLift (Mod.regular (scalarRingObj Λ.X)) (c j k) := by
    have h := scalarSections.{u}.mapMod_map_matrix Λ.X b
    rw [hb] at h
    refine Eq.trans ?_ h
    simp only [ρQ, p, Γ, Retract.trans_r, Retract.trans_i, Retract.map_r, Retract.map_i,
      Retract.ofIso, Functor.map_comp, Category.assoc]
  refine ⟨Γ.obj (M.obj P), n, ⟨ρQ⟩, ⟨?_⟩⟩
  -- Both sides are retracts of the free module on T for the same scalar matrix.
  let FT := (upperStarFromPoint T).mapMod Λ.X
  let E := finiteConstantScalarExtension Λ.X T
  let ρT : Retract (FT.obj (M.obj P)) (Mod.finiteFree (condensedRingObj Λ.X T) n) :=
    (ρ₁.map FT).trans (Retract.ofIso (pointFreeIso Λ.X T n))
  let ρE : Retract (E.obj (Γ.obj (M.obj P))) (Mod.finiteFree (condensedRingObj Λ.X T) n) :=
    (ρQ.map E).trans (Retract.ofIso (scalarFreeIso Λ.X T n))
  have hT : ρT.r ≫ ρT.i = scalarMatrix Λ.X T c := by
    refine Eq.trans ?_ (pointMatrix_map Λ.X T c)
    rw [← hp]
    simp only [ρT, p, FT, Retract.trans_r, Retract.trans_i, Retract.map_r, Retract.map_i,
      Retract.ofIso, Functor.map_comp, Category.assoc]
  have hE : ρE.r ≫ ρE.i = scalarMatrix Λ.X T c := by
    refine Eq.trans ?_ (scalarMatrix_map Λ.X T c)
    rw [← hq]
    simp only [ρE, E, Retract.trans_r, Retract.trans_i, Retract.map_r, Retract.map_i,
      Retract.ofIso, Functor.map_comp, Category.assoc]
  exact (Mod.comap (coefficientMap a T)).mapIso
      (finiteComparisonRealizationConstantIso A eR T P) ≪≫
    ((upperStarFromPoint T).mapModComapIso a).symm.app _ ≪≫
    ρT.isoCokernel ≪≫ cokernelIsoOfEq (by rw [hT, hE]) ≪≫ ρE.isoCokernel.symm

end AlgebraicGeometry.ProEtale.CondensedRing
