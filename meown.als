//NOTA: Qualquer referência no seguinte texto a elevadores e andares é pura
//coincidência e não deve ser levada a sério.
open util/ordering[State]

sig State {
	localActual: Carruagem set -> one Paragem
}

sig Paragem {
	seguinte: lone Paragem,
	chamada: one Direccao
}

sig Carruagem {
	movimento: one Direccao
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
	no p1: Paragem | p1 in p1.^seguinte
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
pred movimento[s, s': State, c1: Carruagem] {
	//get Paragem da Carruagem from localActual
	//if Carruagem.direccao Direita
	// ++ Carruagem -> Paragem.seguinte
	//if Carruagem.direccao Esquerda
	// ++ Carruagem -> seguinte.Paragem
	//if Carruagem.direccao Nenhuma
	// carruagem fica igual
	//s'.localActual = s.localActual	 - (c -> Paragem) + (c -> p)
	let p1 = s.localActual[c1] 
	{
		(c1.movimento = Direita) => 
				(s'.localActual = s.localActual ++ (c1 -> p1.seguinte)) 
		else 
				((c1.movimento = Esquerda) => 
						(s'.localActual = s.localActual ++ (c1 -> seguinte.p1)) 
				else
						(s'.localActual = s.localActual))
	}
}

pred movAll[s, s': State] {
	all c1: Carruagem | movimento[s,s',c1]
}

//------------------------------------------------------------------------------------------------
//--------------------------------------- Cheques (em branco ou não) -------------------
//------------------------------------------------------------------------------------------------

fact motor {
	#Paragem > 3
	all s : State, s' : s.next | movAll[s,s'] && s != s'
}

assert verMovimentoSenaoTamosLixadosNaoSeVeNada {
	//diz que entre transições de estados não há diferenças logo
	//ele vai mostrar apenas estados em que há diferenças
	all s: State, s': s.next | #(s.localActual - s'.localActual) < 1
}

check verMovimentoSenaoTamosLixadosNaoSeVeNada for 6
//run {} for 4 but 5 Paragem, 5 Carruagem
