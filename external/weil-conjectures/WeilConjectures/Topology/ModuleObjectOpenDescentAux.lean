/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Topology.ModuleCompatibleFamilySheaf

/-! Auxiliary descent theorem assuming diagonal transition maps are identities.
Source: Stacks Project, Sheaves, Lemmas 00AL and 00AM.
(blueprint: lem-weil-pbc-module-object-open-descent-aux-diagonal)
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

-- The dependent Over-site naturality and scalar restrictions require extra elaboration.
/-- Descent of module objects when the diagonal transition maps are identities.
The proof constructs compatible families on each open and glues them componentwise;
the diagonal assumption is used to show the projection and reconstruction maps are
mutual inverses.
(blueprint: lem-weil-pbc-module-object-open-descent-aux-diagonal)
Proof: construct the compatible-family sheaf componentwise, glue sections using local
sheaf axioms, and use diagonal and cocycle identities to prove projection and
reconstruction are inverse. -/
theorem module_object_open_descent_aux
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (φij : ∀ i j : I,
      (SheafOfModules.overMap (moduleRings X) (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj
          (Fi i) ≅
        (SheafOfModules.overMap (moduleRings X)
          (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    (hdiag : ∀ (i : I) (W : Opens X) (hi : W ≤ U i),
      (φij i i).hom.val.app (op (Over.mk (homOfLE (le_inf hi hi)))) =
        𝟙 _) :
    (∀ (i j k : I) (W : Opens X)
      (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
      (φij i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
        (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (φij j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk))))) →
    ∃ (H : SheafOfModules.{max u v} (moduleRings X))
      (φi : ∀ i : I, H.over (U i) ≅ Fi i),
      ∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
        (φi i).hom.val.app (op (Over.mk (homOfLE hi))) ≫
            (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) =
          (φi j).hom.val.app (op (Over.mk (homOfLE hj))) := by
  intro hcoc
  obtain ⟨H, π, hH⟩ := module_compatible_family_sheaf X I U hcover Fi φij
  have heval (V : Opens X) (i : I) (hi : V ≤ U i) (s : H.val.obj (op V)) :
      openModuleFamilyEval X I U Fi H π V s i V hi le_rfl =
        (π i).val.app (op (Over.mk (homOfLE hi))) s := by
    simp [openModuleFamilyEval]
  have hbij (i : I) (V : Opens X) (hi : V ≤ U i) :
      Function.Bijective ((π i).val.app (op (Over.mk (homOfLE hi)))) := by
    constructor
    · intro s t hst
      apply (hH V).2.1
      funext j W hj hWV
      rw [← ((hH V).1 s).2 i j W (hWV.trans hi) hj hWV,
        ← ((hH V).1 t).2 i j W (hWV.trans hi) hj hWV]
      congr 1
      rw [← ((hH V).1 s).1 i V W hi le_rfl hWV,
        ← ((hH V).1 t).1 i V W hi le_rfl hWV, heval, heval, hst]
    · intro t
      let a : OpenModuleFamily X I U Fi V := fun j W hj hWV ↦
        (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf (hWV.trans hi) hj))))
          ((Fi i).val.map (Over.homMk (homOfLE hWV)).op t)
      have ha : OpenModuleFamilyCoherent X I U Fi φij V a := by
        constructor
        · intro j W Z hj hWV hZW
          dsimp [a]
          have hn := PresheafOfModules.naturality_apply (φij i j).hom.val
            (Over.homMk (homOfLE hZW) :
              Over.mk (homOfLE (le_inf ((hZW.trans hWV).trans hi) (hZW.trans hj))) ⟶
                Over.mk (homOfLE (le_inf (hWV.trans hi) hj))).op
            ((Fi i).val.map (Over.homMk (homOfLE hWV)).op t)
          change (φij i j).hom.val.app
            (op (Over.mk (homOfLE (le_inf ((hZW.trans hWV).trans hi) (hZW.trans hj)))))
              ((Fi i).val.map (Over.homMk (homOfLE hZW) :
                Over.mk (homOfLE ((hZW.trans hWV).trans hi)) ⟶
                  Over.mk (homOfLE (hWV.trans hi))).op
                ((Fi i).val.map (Over.homMk (homOfLE hWV) :
                  Over.mk (homOfLE (hWV.trans hi)) ⟶ Over.mk (homOfLE hi)).op t)) =
            (Fi j).val.map (Over.homMk (homOfLE hZW) :
              Over.mk (homOfLE (hZW.trans hj)) ⟶ Over.mk (homOfLE hj)).op
              ((φij i j).hom.val.app
                (op (Over.mk (homOfLE (le_inf (hWV.trans hi) hj))))
                  ((Fi i).val.map (Over.homMk (homOfLE hWV) :
                    Over.mk (homOfLE (hWV.trans hi)) ⟶ Over.mk (homOfLE hi)).op t)) at hn
          have hh :
              (Over.homMk (homOfLE hWV) :
                Over.mk (homOfLE (hWV.trans hi)) ⟶ Over.mk (homOfLE hi)).op ≫
              (Over.homMk (homOfLE hZW) :
                Over.mk (homOfLE ((hZW.trans hWV).trans hi)) ⟶
                  Over.mk (homOfLE (hWV.trans hi))).op =
              (Over.homMk (homOfLE (hZW.trans hWV)) :
                Over.mk (homOfLE ((hZW.trans hWV).trans hi)) ⟶
                  Over.mk (homOfLE hi)).op := by rfl
          rw [← PresheafOfModules.map_comp_apply, hh] at hn
          exact hn.symm
        · intro j k W hj hk hWV
          dsimp [a]
          exact (CategoryTheory.congr_fun (hcoc i j k W (hWV.trans hi) hj hk)
            ((Fi i).val.map (Over.homMk (homOfLE hWV)).op t)).symm
      obtain ⟨s, hs⟩ := (hH V).2.2 a ha
      refine ⟨s, ?_⟩
      have hs' := congrFun (congrFun (congrFun (congrFun hs i) V) hi) le_rfl
      rw [heval] at hs'
      simp only [a, hdiag i V hi, ModuleCat.id_apply] at hs'
      change (π i).val.app (op (Over.mk (homOfLE hi))) s =
        (Fi i).val.map (𝟙 (op (Over.mk (homOfLE hi)))) t at hs'
      simpa using hs'
  have hπ (i : I) : IsIso (π i) := by
    have happ (V : (Over (U i))ᵒᵖ) : IsIso ((π i).val.app V) := by
      exact (ConcreteCategory.isIso_iff_bijective _).2
        (hbij i V.unop.left (leOfHom V.unop.hom))
    let e := PresheafOfModules.isoMk (fun V ↦ asIso ((π i).val.app V))
      (fun {_ _} f ↦ (π i).val.naturality f)
    have : IsIso (π i).val := by
      change IsIso e.hom
      infer_instance
    have : IsIso ((SheafOfModules.forget _).map (π i)) := ‹IsIso (π i).val›
    exact isIso_of_reflects_iso (π i) (SheafOfModules.forget _)
  let φi : ∀ i : I, H.over (U i) ≅ Fi i := fun i ↦ asIso (π i)
  refine ⟨H, φi, ?_⟩
  intro i j W hi hj
  ext s
  have hc := ((hH W).1 s).2 i j W hi hj le_rfl
  change (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj))))
      ((π i).val.app (op (Over.mk (homOfLE hi))) s) =
        (π j).val.app (op (Over.mk (homOfLE hj))) s
  simpa only [heval] using hc

end AlgebraicGeometry
