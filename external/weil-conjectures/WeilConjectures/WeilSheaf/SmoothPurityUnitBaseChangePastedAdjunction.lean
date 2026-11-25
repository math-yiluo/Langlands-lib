/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeComp
public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp

/-! # Unit base change for specified factorizations of the left adjoints -/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  {F : A ⥤ B} {FR : B ⥤ A} (adjF : F ⊣ FR)
  {G : B ⥤ C} {GR : C ⥤ B} (adjG : G ⊣ GR)
  {H : A ⥤ C} {HR : C ⥤ A} (adjH : H ⊣ HR)
  {F' : A' ⥤ B'} {FR' : B' ⥤ A'} (adjF' : F' ⊣ FR')
  {G' : B' ⥤ C'} {GR' : C' ⥤ B'} (adjG' : G' ⊣ GR')
  {H' : A' ⥤ C'} {HR' : C' ⥤ A'} (adjH' : H' ⊣ HR')
  {TA : A ⥤ A'} {TB : B ⥤ B'} {TC : C ⥤ C'}
  (eF : F ⋙ TB ≅ TA ⋙ F') (eG : G ⋙ TC ≅ TB ⋙ G')
  (h : H ≅ F ⋙ G) (h' : H' ≅ F' ⋙ G')
  {U : C} {U' : C'} (ε : TC.obj U ⟶ U')

/-- A pasted unit base change is invertible for any specified factorizations of the
left adjoints. The right-adjoint composition comparisons are their canonical mates. -/
theorem isIso_unitBaseChange_pastedAdjunction
    [IsIso ((mateEquiv adjF adjF' (inv eF.hom)).app (GR.obj U))]
    [IsIso (unitBaseChange adjG adjG' eG.hom ε)] :
    IsIso (unitBaseChange adjH adjH'
      (Functor.isoWhiskerRight h TC ≪≫ compForgetIso eF eG ≪≫
        Functor.isoWhiskerLeft TA h'.symm).hom ε) := by
  let ρ := conjugateIsoEquiv adjH (adjF.comp adjG) h.symm
  let ρ' := conjugateIsoEquiv adjH' (adjF'.comp adjG') h'.symm
  have hρ : ∀ K, G.map (F.map (ρ.hom.app K)) ≫ G.map (adjF.counit.app _) ≫
      adjG.counit.app K = h.inv.app _ ≫ adjH.counit.app K := by
    intro K
    have he := conjugateEquiv_counit adjH (adjF.comp adjG) h.inv K
    simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj] at he
    exact he
  have hρ' : ∀ K, G'.map (F'.map (ρ'.hom.app K)) ≫ G'.map (adjF'.counit.app _) ≫
      adjG'.counit.app K = h'.inv.app _ ≫ adjH'.counit.app K := by
    intro K
    have he := conjugateEquiv_counit adjH' (adjF'.comp adjG') h'.inv K
    simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj] at he
    exact he
  apply isIso_unitBaseChange_comp adjF adjG adjH adjF' adjG' adjH'
    eF.hom eG.hom _ h h' _ ρ hρ ρ' hρ' ε
  constructor
  intro K
  simp [compForgetIso]

end CategoryTheory.Adjunction
