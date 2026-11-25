/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Transport and normalization of tensor representatives
Source: Stacks 0FPT, 06YU and 07A4.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.MonoidalCategory
namespace WeilConjectures
attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  coefficientTotalTensor coefficientKFlatInclusion
attribute [local irreducible] SheafOfModules.monoidalCategory coefficientTensorGenerator
  CoefficientTensorModels.iso DerivedCategory.Q
section CoherenceTransfer

universe a b x y
variable {D : Type a} [Category.{x} D] {E' : Type b} [Category.{y} E']
  {H : Dᵒᵖ × D ⥤ D} {HU : E'ᵒᵖ × E' ⥤ E'}
  (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
  {r : D ⥤ E'}
variable (rho : ∀ L M : D, r.obj (S.tensor.obj (L, M)) ≅
    SU.tensor.obj (r.obj L, r.obj M))
  (rho_naturality : ∀ (L M L' M' : D) (f : L ⟶ L') (g : M ⟶ M'),
    r.map (S.tensor.map (f, g)) ≫ (rho L' M').hom =
      (rho L M).hom ≫ SU.tensor.map (r.map f, r.map g))
include rho rho_naturality
private theorem nested_left_model
    {P Q N PQ L : D} {PU QU NU PQU LU : E'}
    (i : PQ ≅ S.tensor.obj (P, Q)) (iL : L ≅ S.tensor.obj (PQ, N))
    (j : PQU ≅ SU.tensor.obj (PU, QU)) (jL : LU ≅ SU.tensor.obj (PQU, NU))
    (aP : r.obj P ≅ PU) (aQ : r.obj Q ≅ QU) (aN : r.obj N ≅ NU)
    (c : r.obj PQ ≅ PQU) (cL : r.obj L ≅ LU)
    (h : r.map i.hom ≫ (rho P Q).hom ≫
      SU.tensor.map (aP.hom, aQ.hom) = c.hom ≫ j.hom)
    (hL : r.map iL.hom ≫ (rho PQ N).hom ≫
      SU.tensor.map (c.hom, aN.hom) = cL.hom ≫ jL.hom) :
    r.map (iL.hom ≫ S.tensor.map (i.hom, 𝟙 N)) ≫
      (rho (S.tensor.obj (P, Q)) N).hom ≫
      SU.tensor.map ((rho P Q).hom, 𝟙 (r.obj N)) ≫
      SU.tensor.map
        (X := (SU.tensor.obj (r.obj P, r.obj Q), r.obj N))
        (Y := (SU.tensor.obj (PU, QU), NU))
        (SU.tensor.map (aP.hom, aQ.hom), aN.hom) =
      cL.hom ≫ jL.hom ≫ SU.tensor.map (j.hom, 𝟙 NU) := by
  let := S.monoidal
  let := SU.monoidal
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (rho_naturality _ _ _ _ _ _)]
  simp only [← Category.assoc, ← SU.tensor.map_comp]
  simp only [prod_comp, Prod.mkHom, r.map_id, Category.id_comp, Category.comp_id,
    Category.assoc]
  change r.map iL.hom ≫ (rho PQ N).hom ≫
    SU.tensor.map (X := (r.obj PQ, r.obj N))
      (Y := (SU.tensor.obj (PU, QU), NU))
      (r.map i.hom ≫ (rho P Q).hom ≫
        SU.tensor.map (aP.hom, aQ.hom), aN.hom) = _
  rw [h]
  have he : SU.tensor.map (X := (r.obj PQ, r.obj N))
      (Y := (SU.tensor.obj (PU, QU), NU)) (c.hom ≫ j.hom, aN.hom) =
      SU.tensor.map (X := (r.obj PQ, r.obj N)) (Y := (PQU, NU))
        (c.hom, aN.hom) ≫ SU.tensor.map
        (X := (PQU, NU)) (Y := (SU.tensor.obj (PU, QU), NU)) (j.hom, 𝟙 NU) := by
    rw [← SU.tensor.map_comp]
    simp only [prod_comp, Category.comp_id]
  rw [he]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ SU.tensor.map (X := (PQU, NU))
      (Y := (SU.tensor.obj (PU, QU), NU)) (j.hom, 𝟙 NU)) hL

private theorem nested_right_model
    {P Q N QN L : D} {PU QU NU QNU LU : E'}
    (i : QN ≅ S.tensor.obj (Q, N)) (iL : L ≅ S.tensor.obj (P, QN))
    (j : QNU ≅ SU.tensor.obj (QU, NU)) (jL : LU ≅ SU.tensor.obj (PU, QNU))
    (aP : r.obj P ≅ PU) (aQ : r.obj Q ≅ QU) (aN : r.obj N ≅ NU)
    (c : r.obj QN ≅ QNU) (cL : r.obj L ≅ LU)
    (h : r.map i.hom ≫ (rho Q N).hom ≫
      SU.tensor.map (aQ.hom, aN.hom) = c.hom ≫ j.hom)
    (hL : r.map iL.hom ≫ (rho P QN).hom ≫
      SU.tensor.map (aP.hom, c.hom) = cL.hom ≫ jL.hom) :
    r.map (iL.hom ≫ S.tensor.map (𝟙 P, i.hom)) ≫
      (rho P (S.tensor.obj (Q, N))).hom ≫
      SU.tensor.map (𝟙 (r.obj P), (rho Q N).hom) ≫
      SU.tensor.map
        (X := (r.obj P, SU.tensor.obj (r.obj Q, r.obj N)))
        (Y := (PU, SU.tensor.obj (QU, NU)))
        (aP.hom, SU.tensor.map (aQ.hom, aN.hom)) =
      cL.hom ≫ jL.hom ≫ SU.tensor.map (𝟙 PU, j.hom) := by
  let := S.monoidal
  let := SU.monoidal
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (rho_naturality _ _ _ _ _ _)]
  simp only [← Category.assoc, ← SU.tensor.map_comp]
  simp only [prod_comp, Prod.mkHom, r.map_id, Category.id_comp, Category.comp_id,
    Category.assoc]
  change r.map iL.hom ≫ (rho P QN).hom ≫
    SU.tensor.map (X := (r.obj P, r.obj QN))
      (Y := (PU, SU.tensor.obj (QU, NU)))
      (aP.hom, r.map i.hom ≫ (rho Q N).hom ≫
        SU.tensor.map (aQ.hom, aN.hom)) = _
  rw [h]
  have he : SU.tensor.map (X := (r.obj P, r.obj QN))
      (Y := (PU, SU.tensor.obj (QU, NU))) (aP.hom, c.hom ≫ j.hom) =
      SU.tensor.map (X := (r.obj P, r.obj QN)) (Y := (PU, QNU))
        (aP.hom, c.hom) ≫ SU.tensor.map
        (X := (PU, QNU)) (Y := (PU, SU.tensor.obj (QU, NU))) (𝟙 PU, j.hom) := by
    rw [← SU.tensor.map_comp]
    simp only [prod_comp, Category.comp_id]
  rw [he]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ SU.tensor.map (X := (PU, QNU))
      (Y := (PU, SU.tensor.obj (QU, NU))) (𝟙 PU, j.hom)) hL
-- The associativity square has dependent comparison endpoints.
omit rho_naturality in
private theorem associator_of_models :
    ∀ {P Q N X Y : D} {PU QU NU XU YU : E'}
    (i : X ≅ S.tensor.obj (S.tensor.obj (P, Q), N))
    (i' : Y ≅ S.tensor.obj (P, S.tensor.obj (Q, N)))
    (j : XU ≅ SU.tensor.obj (SU.tensor.obj (PU, QU), NU))
    (j' : YU ≅ SU.tensor.obj (PU, SU.tensor.obj (QU, NU)))
    (aP : r.obj P ≅ PU) (aQ : r.obj Q ≅ QU) (aN : r.obj N ≅ NU)
    (c : r.obj X ≅ XU) (c' : r.obj Y ≅ YU)
    (b : X ⟶ Y) (bU : XU ⟶ YU)
    (_hL : r.map i.hom ≫ (rho (S.tensor.obj (P, Q)) N).hom ≫
      SU.tensor.map (X := (r.obj (S.tensor.obj (P, Q)), r.obj N))
        (Y := (SU.tensor.obj (r.obj P, r.obj Q), r.obj N))
        ((rho P Q).hom, 𝟙 (r.obj N)) ≫
      SU.tensor.map (X := (SU.tensor.obj (r.obj P, r.obj Q), r.obj N))
        (Y := (SU.tensor.obj (PU, QU), NU))
        (SU.tensor.map (X := (r.obj P, r.obj Q)) (Y := (PU, QU))
          (aP.hom, aQ.hom), aN.hom) =
      c.hom ≫ j.hom)
    (_hR : r.map i'.hom ≫ (rho P (S.tensor.obj (Q, N))).hom ≫
      SU.tensor.map (X := (r.obj P, r.obj (S.tensor.obj (Q, N))))
        (Y := (r.obj P, SU.tensor.obj (r.obj Q, r.obj N)))
        (𝟙 (r.obj P), (rho Q N).hom) ≫
      SU.tensor.map (X := (r.obj P, SU.tensor.obj (r.obj Q, r.obj N)))
        (Y := (PU, SU.tensor.obj (QU, NU)))
        (aP.hom, SU.tensor.map (X := (r.obj Q, r.obj N)) (Y := (QU, NU))
          (aQ.hom, aN.hom)) =
      c'.hom ≫ j'.hom)
    (_hb : i.hom ≫ (S.monoidal.associator P Q N).hom = b ≫ i'.hom)
    (_hbU : j.hom ≫ (SU.monoidal.associator PU QU NU).hom = bU ≫ j'.hom)
    (_hc : r.map b ≫ c'.hom = c.hom ≫ bU),
    r.map (S.monoidal.associator P Q N).hom ≫
      (rho P (S.tensor.obj (Q, N))).hom ≫
      SU.tensor.map (X := (r.obj P, r.obj (S.tensor.obj (Q, N))))
        (Y := (r.obj P, SU.tensor.obj (r.obj Q, r.obj N)))
        (𝟙 (r.obj P), (rho Q N).hom) =
      (rho (S.tensor.obj (P, Q)) N).hom ≫
        SU.tensor.map (X := (r.obj (S.tensor.obj (P, Q)), r.obj N))
          (Y := (SU.tensor.obj (r.obj P, r.obj Q), r.obj N))
          ((rho P Q).hom, 𝟙 (r.obj N)) ≫
        (SU.monoidal.associator (r.obj P) (r.obj Q) (r.obj N)).hom := by
  let := S.monoidal
  let := SU.monoidal
  intro P Q N X Y PU QU NU XU YU i i' j j' aP aQ aN c c' b bU hL hR hb hbU hc
  simp only [CoefficientClosedStructure.tensor, tensor_obj, tensor_map,
    tensorHom_id, id_tensorHom] at hL hR ⊢
  have hi : IsIso (aP.hom ⊗ₘ (aQ.hom ⊗ₘ aN.hom)) := inferInstance
  apply (cancel_epi (r.map i.hom)).mp
  apply (cancel_mono (aP.hom ⊗ₘ (aQ.hom ⊗ₘ aN.hom))).mp
  calc
    _ = r.map b ≫ (r.map i'.hom ≫ (rho P (Q ⊗ N)).hom ≫
        r.obj P ◁ (rho Q N).hom ≫ (aP.hom ⊗ₘ (aQ.hom ⊗ₘ aN.hom))) := by
      simp only [← r.map_comp, ← Category.assoc, hb]
    _ = r.map b ≫ c'.hom ≫ j'.hom := by rw [hR]
    _ = c.hom ≫ bU ≫ j'.hom := by rw [← Category.assoc, hc, Category.assoc]
    _ = c.hom ≫ j.hom ≫ (α_ PU QU NU).hom := by
      rw [← hbU]
    _ = _ := by
      rw [← Category.assoc, ← hL]
      simp only [Category.assoc]
      rw [MonoidalCategory.associator_naturality]
section RepresentativeComparison
universe a' b' x' y'
variable {V : Type a'} [Category.{x'} V] {W : Type b'} [Category.{y'} W]

/-- Transport associativity through four binary representative squares.
Source: Stacks 0FPT and 07A4
(blueprint: lem-pur-ringed-tensor-representative-transport).
Proof: combine the two inner and two outer squares by naturality of the binary
comparison. The two nested model isomorphisms conjugate the structural associators.
Naturality of the quotient comparison transports the given chain equality. Cancel
the source and target nested model isomorphisms to obtain the asserted equation. -/
theorem coefficientRepresentativeTensorComparison_associativity
    (q : V ⥤ D) (qU : W ⥤ E') (F : V ⥤ W)
    (A : V × V ⥤ V) (AU : W × W ⥤ W) (α : q ⋙ r ≅ F ⋙ qU)
    (P Q N : V)
    (γPQ : F.obj (A.obj (P, Q)) ≅ AU.obj (F.obj P, F.obj Q))
    (γQN : F.obj (A.obj (Q, N)) ≅ AU.obj (F.obj Q, F.obj N))
    (γL : F.obj (A.obj (A.obj (P, Q), N)) ≅
      AU.obj (F.obj (A.obj (P, Q)), F.obj N))
    (γR : F.obj (A.obj (P, A.obj (Q, N))) ≅
      AU.obj (F.obj P, F.obj (A.obj (Q, N))))
    (a : A.obj (A.obj (P, Q), N) ≅ A.obj (P, A.obj (Q, N)))
    (aU : AU.obj (AU.obj (F.obj P, F.obj Q), F.obj N) ≅
      AU.obj (F.obj P, AU.obj (F.obj Q, F.obj N)))
    (tPQ : q.obj (A.obj (P, Q)) ≅ S.tensor.obj (q.obj P, q.obj Q))
    (tQN : q.obj (A.obj (Q, N)) ≅ S.tensor.obj (q.obj Q, q.obj N))
    (tL : q.obj (A.obj (A.obj (P, Q), N)) ≅
      S.tensor.obj (q.obj (A.obj (P, Q)), q.obj N))
    (tR : q.obj (A.obj (P, A.obj (Q, N))) ≅
      S.tensor.obj (q.obj P, q.obj (A.obj (Q, N))))
    (uPQ : qU.obj (AU.obj (F.obj P, F.obj Q)) ≅
      SU.tensor.obj (qU.obj (F.obj P), qU.obj (F.obj Q)))
    (uQN : qU.obj (AU.obj (F.obj Q, F.obj N)) ≅
      SU.tensor.obj (qU.obj (F.obj Q), qU.obj (F.obj N)))
    (uL : qU.obj (AU.obj (AU.obj (F.obj P, F.obj Q), F.obj N)) ≅
      SU.tensor.obj (qU.obj (AU.obj (F.obj P, F.obj Q)), qU.obj (F.obj N)))
    (uR : qU.obj (AU.obj (F.obj P, AU.obj (F.obj Q, F.obj N))) ≅
      SU.tensor.obj (qU.obj (F.obj P), qU.obj (AU.obj (F.obj Q, F.obj N))))
    (uL₀ : qU.obj (AU.obj (F.obj (A.obj (P, Q)), F.obj N)) ≅
      SU.tensor.obj (qU.obj (F.obj (A.obj (P, Q))), qU.obj (F.obj N)))
    (uR₀ : qU.obj (AU.obj (F.obj P, F.obj (A.obj (Q, N)))) ≅
      SU.tensor.obj (qU.obj (F.obj P), qU.obj (F.obj (A.obj (Q, N)))))
    (hePQ : r.map tPQ.hom ≫ (rho (q.obj P) (q.obj Q)).hom ≫
      SU.tensor.map (X := (r.obj (q.obj P), r.obj (q.obj Q)))
        (Y := (qU.obj (F.obj P), qU.obj (F.obj Q))) (α.hom.app P, α.hom.app Q) =
      α.hom.app (A.obj (P, Q)) ≫ qU.map γPQ.hom ≫ uPQ.hom)
    (heQN : r.map tQN.hom ≫ (rho (q.obj Q) (q.obj N)).hom ≫
      SU.tensor.map (X := (r.obj (q.obj Q), r.obj (q.obj N)))
        (Y := (qU.obj (F.obj Q), qU.obj (F.obj N))) (α.hom.app Q, α.hom.app N) =
      α.hom.app (A.obj (Q, N)) ≫ qU.map γQN.hom ≫ uQN.hom)
    (heL : r.map tL.hom ≫ (rho (q.obj (A.obj (P, Q))) (q.obj N)).hom ≫
      SU.tensor.map (X := (r.obj (q.obj (A.obj (P, Q))), r.obj (q.obj N)))
        (Y := (qU.obj (F.obj (A.obj (P, Q))), qU.obj (F.obj N)))
        (α.hom.app (A.obj (P, Q)), α.hom.app N) =
      α.hom.app (A.obj (A.obj (P, Q), N)) ≫ qU.map γL.hom ≫ uL₀.hom)
    (heR : r.map tR.hom ≫ (rho (q.obj P) (q.obj (A.obj (Q, N)))).hom ≫
      SU.tensor.map (X := (r.obj (q.obj P), r.obj (q.obj (A.obj (Q, N)))))
        (Y := (qU.obj (F.obj P), qU.obj (F.obj (A.obj (Q, N)))))
        (α.hom.app P, α.hom.app (A.obj (Q, N))) =
      α.hom.app (A.obj (P, A.obj (Q, N))) ≫ qU.map γR.hom ≫ uR₀.hom)
    (hea : tL.hom ≫ S.tensor.map (X := (q.obj (A.obj (P, Q)), q.obj N))
        (Y := (S.tensor.obj (q.obj P, q.obj Q), q.obj N)) (tPQ.hom, 𝟙 _) ≫
      (S.monoidal.associator (q.obj P) (q.obj Q) (q.obj N)).hom =
      q.map a.hom ≫ tR.hom ≫ S.tensor.map
        (X := (q.obj P, q.obj (A.obj (Q, N))))
        (Y := (q.obj P, S.tensor.obj (q.obj Q, q.obj N))) (𝟙 _, tQN.hom))
    (heaU : uL.hom ≫ SU.tensor.map
        (X := (qU.obj (AU.obj (F.obj P, F.obj Q)), qU.obj (F.obj N)))
        (Y := (SU.tensor.obj (qU.obj (F.obj P), qU.obj (F.obj Q)), qU.obj (F.obj N)))
        (uPQ.hom, 𝟙 _) ≫
      (SU.monoidal.associator (qU.obj (F.obj P)) (qU.obj (F.obj Q)) (qU.obj (F.obj N))).hom =
      qU.map aU.hom ≫ uR.hom ≫ SU.tensor.map
        (X := (qU.obj (F.obj P), qU.obj (AU.obj (F.obj Q, F.obj N))))
        (Y := (qU.obj (F.obj P), SU.tensor.obj (qU.obj (F.obj Q), qU.obj (F.obj N))))
        (𝟙 _, uQN.hom))
    (hnL : qU.map (AU.map (X := (F.obj (A.obj (P, Q)), F.obj N))
        (Y := (AU.obj (F.obj P, F.obj Q), F.obj N)) (γPQ.hom, 𝟙 _)) ≫ uL.hom =
      uL₀.hom ≫ SU.tensor.map
        (X := (qU.obj (F.obj (A.obj (P, Q))), qU.obj (F.obj N)))
        (Y := (qU.obj (AU.obj (F.obj P, F.obj Q)), qU.obj (F.obj N)))
        (qU.map γPQ.hom, 𝟙 _))
    (hnR : qU.map (AU.map (X := (F.obj P, F.obj (A.obj (Q, N))))
        (Y := (F.obj P, AU.obj (F.obj Q, F.obj N))) (𝟙 _, γQN.hom)) ≫ uR.hom =
      uR₀.hom ≫ SU.tensor.map
        (X := (qU.obj (F.obj P), qU.obj (F.obj (A.obj (Q, N)))))
        (Y := (qU.obj (F.obj P), qU.obj (AU.obj (F.obj Q, F.obj N))))
        (𝟙 _, qU.map γQN.hom))
    (hc : F.map a.hom ≫ γR.hom ≫ AU.map
        (X := (F.obj P, F.obj (A.obj (Q, N))))
        (Y := (F.obj P, AU.obj (F.obj Q, F.obj N))) (𝟙 _, γQN.hom) =
      γL.hom ≫ AU.map (X := (F.obj (A.obj (P, Q)), F.obj N))
        (Y := (AU.obj (F.obj P, F.obj Q), F.obj N)) (γPQ.hom, 𝟙 _) ≫ aU.hom) :
    r.map (S.monoidal.associator (q.obj P) (q.obj Q) (q.obj N)).hom ≫
      (rho (q.obj P) (S.tensor.obj (q.obj Q, q.obj N))).hom ≫
      SU.tensor.map (X := (r.obj (q.obj P), r.obj (S.tensor.obj (q.obj Q, q.obj N))))
        (Y := (r.obj (q.obj P), SU.tensor.obj (r.obj (q.obj Q), r.obj (q.obj N))))
        (𝟙 _, (rho (q.obj Q) (q.obj N)).hom) =
      (rho (S.tensor.obj (q.obj P, q.obj Q)) (q.obj N)).hom ≫
      SU.tensor.map (X := (r.obj (S.tensor.obj (q.obj P, q.obj Q)), r.obj (q.obj N)))
        (Y := (SU.tensor.obj (r.obj (q.obj P), r.obj (q.obj Q)), r.obj (q.obj N)))
        ((rho (q.obj P) (q.obj Q)).hom, 𝟙 _) ≫
      (SU.monoidal.associator (r.obj (q.obj P)) (r.obj (q.obj Q)) (r.obj (q.obj N))).hom := by
  let i := tL ≪≫ S.tensor.mapIso (tPQ.prod (Iso.refl _))
  let i' := tR ≪≫ S.tensor.mapIso ((Iso.refl _).prod tQN)
  let j := uL ≪≫ SU.tensor.mapIso (uPQ.prod (Iso.refl _))
  let j' := uR ≪≫ SU.tensor.mapIso ((Iso.refl _).prod uQN)
  let c := α.app (A.obj (A.obj (P, Q), N)) ≪≫ qU.mapIso γL ≪≫
    qU.mapIso (AU.mapIso (γPQ.prod (Iso.refl (F.obj N))))
  let c' := α.app (A.obj (P, A.obj (Q, N))) ≪≫ qU.mapIso γR ≪≫
    qU.mapIso (AU.mapIso ((Iso.refl (F.obj P)).prod γQN))
  have hL := nested_left_model S SU rho rho_naturality tPQ tL uPQ uL
    (α.app P) (α.app Q) (α.app N)
    (α.app (A.obj (P, Q)) ≪≫ qU.mapIso γPQ) c
    (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] using hePQ) (by
      dsimp only [c, Iso.trans_hom, Functor.mapIso_hom]
      simp only [Category.assoc, Iso.prod_hom, Iso.refl_hom, Prod.mkHom]
      rw [hnL]
      have hh := congrArg (fun f ↦ f ≫ SU.tensor.map
        (X := (qU.obj (F.obj (A.obj (P, Q))), qU.obj (F.obj N)))
        (Y := (qU.obj (AU.obj (F.obj P, F.obj Q)), qU.obj (F.obj N)))
        (qU.map γPQ.hom, 𝟙 _)) heL
      simpa only [Category.assoc, ← SU.tensor.map_comp, prod_comp,
        Category.id_comp, Category.comp_id, Iso.app_hom, Iso.trans_hom,
        Functor.mapIso_hom, Prod.mkHom] using hh)
  have hR := nested_right_model S SU rho rho_naturality tQN tR uQN uR
    (α.app P) (α.app Q) (α.app N)
    (α.app (A.obj (Q, N)) ≪≫ qU.mapIso γQN) c'
    (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] using heQN) (by
      dsimp only [c', Iso.trans_hom, Functor.mapIso_hom]
      simp only [Category.assoc, Iso.prod_hom, Iso.refl_hom, Prod.mkHom]
      rw [hnR]
      have hh := congrArg (fun f ↦ f ≫ SU.tensor.map
        (X := (qU.obj (F.obj P), qU.obj (F.obj (A.obj (Q, N)))))
        (Y := (qU.obj (F.obj P), qU.obj (AU.obj (F.obj Q, F.obj N))))
        (𝟙 _, qU.map γQN.hom)) heR
      simpa only [Category.assoc, ← SU.tensor.map_comp, prod_comp,
        Category.id_comp, Category.comp_id, Iso.app_hom, Iso.trans_hom,
        Functor.mapIso_hom, Prod.mkHom] using hh)
  apply associator_of_models S SU rho i i' j j'
    (α.app P) (α.app Q) (α.app N) c c' (q.map a.hom) (qU.map aU.hom)
    (by
      dsimp only [i, j, Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
        Iso.refl, Prod.mkHom]
      simpa only [Prod.mkHom, Category.assoc] using hL)
    (by
      dsimp only [i', j', Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
        Iso.refl, Prod.mkHom]
      simpa only [Prod.mkHom, Category.assoc] using hR)
    (by
      dsimp only [i, i', Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
        Iso.refl, Prod.mkHom]
      exact (Category.assoc _ _ _).trans hea)
    (by
      dsimp only [j, j', Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
        Iso.refl, Prod.mkHom]
      exact (Category.assoc _ _ _).trans heaU)
  dsimp only [c, c', Iso.trans_hom, Functor.mapIso_hom, Iso.prod, Iso.refl, Prod.mkHom]
  simp only [Category.assoc, Iso.app_hom]
  rewrite [reassoc_of% α.hom.naturality a.hom]
  have hh := congrArg (fun f ↦ α.hom.app _ ≫ qU.map f) hc
  simpa only [Functor.map_comp, Category.assoc] using hh

end RepresentativeComparison
end CoherenceTransfer

section ModelNaturality
universe c v r d
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{d} (RingedTensorModules.{c, v, r} J R)]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, d} J R))
  (T : CoefficientTensorModels.{r, c, v, d} J R S)
private theorem model_iso_naturality
    (P Q P' Q' : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P')
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J R).map (f, g)) ≫
        (T.iso J R S P' Q' hP' hQ').hom =
      (T.iso J R S P Q hP hQ).hom ≫
        S.tensor.map (DerivedCategory.Q.map f, DerivedCategory.Q.map g) := by
  have h := T.comparison.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := ⟨P', hP'⟩) f)
      (ObjectProperty.homMk (X := ⟨Q, hQ⟩) (Y := ⟨Q', hQ'⟩) g))
  unfold CoefficientTensorModels.iso
  dsimp only [coefficientKFlatInclusion, Iso.app_hom,
    Functor.comp_map, Functor.prod_map, Prod.mkHom, ObjectProperty.ι,
    inducedFunctor, ObjectProperty.homMk] at h ⊢
  exact h
/-- Naturality of the fixed simultaneous tensor model in its left input.
Source: Stacks 06YU (blueprint: lem-pur-ringed-tensor-representative-transport).
Proof: specialize naturality of the model comparison to the identity in the right input. -/
theorem coefficientTensorModel_iso_naturality_left
    (P P' Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P')
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (f : P ⟶ P') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J R).map (f, 𝟙 Q)) ≫
        (T.iso J R S P' Q hP' hQ).hom =
      (T.iso J R S P Q hP hQ).hom ≫
        S.tensor.map (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj Q)) := by
  have h := model_iso_naturality J R S T P Q P' Q hP hQ hP' hQ f (𝟙 Q)
  rw [CategoryTheory.Functor.map_id] at h
  exact h

/-- Naturality of the fixed simultaneous tensor model in its right input.
Source: Stacks 06YU (blueprint: lem-pur-ringed-tensor-representative-transport).
Proof: specialize naturality of the model comparison to the identity in the left input. -/
theorem coefficientTensorModel_iso_naturality_right
    (P Q Q' : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q')
    (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J R).map (𝟙 P, g)) ≫
        (T.iso J R S P Q' hP hQ').hom =
      (T.iso J R S P Q hP hQ).hom ≫
        S.tensor.map (𝟙 (DerivedCategory.Q.obj P), DerivedCategory.Q.map g) := by
  have h := model_iso_naturality J R S T P Q P Q' hP hQ hP hQ' (𝟙 P) g
  rw [CategoryTheory.Functor.map_id] at h
  exact h

/-- Associator representatives with the simultaneous K-flat comparisons on both sides.
Source: Stacks 0FPT and 06YU
(blueprint: lem-pur-ringed-tensor-representative-transport).
Proof: take the associator supplied by the ringed tensor coherence. The two total
products of K-flat inputs are K-flat. Its one-K-flat comparisons therefore equal
the fixed simultaneous model comparisons, by tensorIso_both and proof irrelevance.
Rewrite these two equalities in the model equation and retain the pure-triple formula. -/
theorem coefficientTensorModel_associator_representative
    {β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal}
    (K : RingedDerivedTensorCoherence.{c, v, r, d} J R S T β) :
  ∀ P Q N hP hQ hN,
    ∃ a : (coefficientTotalTensor.{r, c, v} J R).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q), N) ≅
      (coefficientTotalTensor.{r, c, v} J R).obj
        (P, (coefficientTotalTensor.{r, c, v} J R).obj (Q, N)),
      (∀ (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
        (hn : pq + r = n) (hn' : p + qr = n) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X r).val.obj U),
        (a.hom.f n).val.app U
          (coefficientTensorGenerator.{r, c, v} J R
            ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N pq r n hn U
            (coefficientTensorGenerator.{r, c, v} J R P Q p q pq hpq U x y) z) =
        coefficientTensorGenerator.{r, c, v} J R P
          ((coefficientTotalTensor.{r, c, v} J R).obj (Q, N)) p qr n hn' U x
          (coefficientTensorGenerator.{r, c, v} J R Q N q r qr hqr U y z)) ∧
      (T.iso J R S ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N
        (coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hN).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)),
            DerivedCategory.Q.obj N))
          (Y := (S.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q),
            DerivedCategory.Q.obj N))
          ((T.iso J R S P Q hP hQ).hom, 𝟙 _) ≫
        (S.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom =
      DerivedCategory.Q.map a.hom ≫
        (T.iso J R S P ((coefficientTotalTensor.{r, c, v} J R).obj (Q, N))
        hP (coefficientTotalTensor_isKFlat.{r, c, v} J R Q N hQ hN)).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj P,
            DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj (Q, N))))
          (Y := (DerivedCategory.Q.obj P,
            S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)))
          (𝟙 _, (T.iso J R S Q N hQ hN).hom) := by
  intro P Q N hP hQ hN
  have hPQ := coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ
  have hQN := coefficientTotalTensor_isKFlat.{r, c, v} J R Q N hQ hN
  obtain ⟨a, ha, hea⟩ := K.associator_model P Q N hP hQ hN
  rw [show K.tensorIso _ N (Or.inr hN) = _ from K.tensorIso_both _ N hPQ hN,
    K.tensorIso_both P _ hP hQN] at hea
  exact ⟨a, ha, hea⟩

end ModelNaturality
end WeilConjectures
