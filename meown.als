//NOTA: Qualquer referência no seguinte texto a elevadores e andares é pura
//coincidência e não deve ser levada a sério.
open util/ordering[State]
 
sig State {
	localActual: Carruagem set -> one Paragem
}
 
sig Paragem {
	seguinte: lone Paragem,
	chamada: one Direccao,
	espera: set Pessoa
}
 
sig Carruagem {
	movimento: one Direccao,
	viagem: set Paragem
}
{
	movimento != Ambas
}
 
sig Pessoa {
	destino: one Paragem,
	passageiros: one Carruagem
}
 
abstract sig Direccao {}
 
one sig Direita, Esquerda, Nenhuma, Ambas extends Direccao {}
 
//------------------------------------------------------------------------------------------------
//----------------------------------- Restringir "seguinte" ---------------------------------
//------------------------------------------------------------------------------------------------
fact naoHaCiclos
{
	all p1: Paragem | p1 in p1.^seguinte
}
 
fact naoHaParagemSeguinteIgualParaDuasParagensDiferentes {
	all p1: Paragem, p2: Paragem, p3:Paragem | 
	(p1 != p3 && (p1.seguinte = p2)) => !(p3.seguinte = p2)
}
 
fact todasParagensLigadas
{
	all p1: Paragem, p2: Paragem | (p1 in p2.*seguinte) || (p1 in *seguinte.p2)
}
//------------------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------------------
 
//------------------------------------------------------------------------------------------------
//--------------------------------------------- Pred's ------------------------------------------
//------------------------------------------------------------------------------------------------
pred movimentacaoCarruagem[s, s': State, c1: Carruagem] {
	let p1 = s.localActual[c1] 
	{
		(movimento[c1] = Nenhuma) implies
				(s'.localActual = s.localActual) 
		else 
		(movimento[c1] = Direita) implies
				(s'.localActual = s.localActual ++ (c1 -> p1.seguinte))
		else
		(movimento[c1] = Esquerda) implies 
				(s'.localActual = s.localActual ++ (c1 -> seguinte.p1))
	}
}
 
//------------------------------------------------------------------------------------------------
//--------------------------------------- Cheques (em branco ou não) -------------------
//------------------------------------------------------------------------------------------------
 
fact motor {
	all c1: Carruagem | c1.movimento = Nenhuma
	all s : State, s' : s.next | some c: Carruagem | some d: Direccao | movimentacaoCarruagem[s,s',c]
}
 
//check verificar for 6
//check verMovimentoSenaoTamosLixadosNaoSeVeNada for 6
run {} for 4
