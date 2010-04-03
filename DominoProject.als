open util/ordering[BoardState] as state


/////////////////
//////Sigs///////
/////////////////
sig Piece {
  left, right : one Int
}

sig Connection{
	left, right: one Piece,
	num: one Int
}

abstract sig Player{}
one sig Player1, Player2 extends Player{}

sig BoardState {
	currentPlayer:one Player,
	links:set Connection, //tabuleiro, o que está na mesa
	deck:set Piece, //Baralho
	played:set Piece, //peças na mesa
	leftPiece,rightPiece: one Piece,//Peças de topo
	leftNum,rightNum: one Int,
	p1Deck,p2Deck:set Piece,//Maos dos jogadores
}
/////////////////
//Parte Estatica//
/////////////////
fact PieceRestrictions{
	all p:Piece | p.left>=0 && p.left<= 6 && p.right>= p.left && p.right<=6//Definir dominio das peças
	all p1, p2:Piece | (p1.left=p2.left && p1.right=p2.right) => p1=p2//Impedir a existencia de peças iguais
}

fact ConnectionConsistency{
	no c:Connection | (c.left.right!=c.num &&c.left.left!=c.num) || (c.right.right!=c.num && c.right.left!=c.num) //Forçar a que a connection seja entre dois numeros iguais
	no c:Connection | c.left=c.right//Impedir a connexão entre a mesma peça
	all c1,c2:Connection | (c1.left=c2.left && c1.right=c2.right) ||(c1.right=c2.left && c1.left=c2.right ) => c1 = c2//Impedir a existencia de conexoes iguais
	all p:Piece | lone c:Connection | c.right=p // Para todas as peças so ha no maximo uma conexão a esquerda
	all p:Piece | lone c:Connection | c.left=p// Para todas as peças so ha no maximo uma conexão a direita
}

fact BoardPiecesRestrictions{

	all b:BoardState | b.p1Deck & b.p2Deck = none//As peças dos diferentes jogadores sao diferentes
	all b:BoardState | b.deck & b.played=none//As peças na mesa e no deck sao diferentes
	all b:BoardState | b.p1Deck & b.played=none//os conjuntos sao dijuntos
	all b:BoardState | b.p2Deck & b.played=none//os conjuntos sao dijuntos
	all b:BoardState | b.p1Deck & b.deck=none//os conjuntos sao dijuntos
	all b:BoardState | b.p2Deck & b.deck=none//os conjuntos sao dijuntos

	all b:BoardState | b.played + b.p1Deck + b.p2Deck + b.deck = Piece//Todas as peças tem que estar em algum dos conjuntos
	all b:BoardState | b.links.left & b.played=b.links.left && b.links.right & b.played=b.links.right
	all c:Connection | some b:BoardState | c in b.links//Obriga a que todas as connexoes estejam associadas a um jogo
	all b:BoardState | b.leftPiece in b.played && b.rightPiece in b.played //Tanto o topo esquerdo como o direito tem de ser peças ja jogadas
}


fact initialState {
	let s0 = state/first | one p:Piece | s0.played = p && s0.leftPiece=p && s0.rightPiece=p &&s0.leftNum=p.left &&s0.rightNum=p.right//select the initial piece
	let s0 = state/first | #s0.p1Deck=1 && #s0.p2Deck=1
}


///////////////////
//Parte Dinamica//
//////////////////



pred fetchPiece [to, to', otherPlayer, otherPlayer': set Piece, s,s':BoardState] {
 (one piece: s.deck{
    s'.deck = s.deck - piece
    to' = to +piece
	//Copiar o estado anterioir
	otherPlayer'=otherPlayer
	s'.played=s.played
	s'.links=s.links
	s'.rightPiece=s.rightPiece
	s'.leftPiece=s.leftPiece
	s'.leftNum=s.leftNum
	s'.rightNum=s.rightNum
	s'.currentPlayer = s.currentPlayer//Nao Alternar os jogadores		
  })
}

pred matchPiece[num,num': Int, p, endPiece :Piece]{//Tenta fazer match com a peça em modo normal ou inverso
	(num=p.right && num'=p.left && endPiece=p)
	||	
	(num=p.left && num'=p.right &&	endPiece=p)
}


pred playPiece [from, from', otherPlayer, otherPlayer': set Piece, s,s':BoardState] {
	one piece: from{
		(matchPiece[s.rightNum,s'.rightNum,piece,s'.rightPiece] || matchPiece[s.leftNum,s'.leftNum,piece,s'.leftPiece]) && {
			(matchPiece[s.rightNum,s'.rightNum,piece,s'.rightPiece]) => {//Right Insert
				s'.leftNum=s.leftNum //Manter o lado esquerdo
				s'.leftPiece=s.leftPiece//Manter o lado esquerdo
            	one c:Connection | c.left=s.rightPiece && c.right=s'.rightPiece && c.num=s.rightNum && s'.links=s.links+c //Adicionar ligação
			}
			else
			(matchPiece[s.leftNum,s'.leftNum,piece,s'.leftPiece]) => {//Left Insert
				s'.rightPiece=s.rightPiece //Manter o lado direito
				s'.rightNum=s.rightNum //Manter o lado direito
    	        one c:Connection | c.left=s'.leftPiece && c.right=s.leftPiece && c.num=s.leftNum && s'.links=s.links+c //Adicionar ligação
			}

		 	from' = from - piece	//remover da origem
    		s'.played = s.played +piece //adicionar às jogadas
			otherPlayer'=otherPlayer//copiar o outro jogador
			s'.deck=s.deck//copiar as peças do baralho
			s.currentPlayer = Player1 => s'.currentPlayer = Player2 else s'.currentPlayer = Player1//Alternar os jogadores	
		}	
	}
}

pred play [me,me', other,other':set Piece, s,s': BoardState]{
	playPiece [me,me', other,other',s,s'] || // =>{}//Jogador Joga
	((!playPiece [me,me', other,other',s,s']) && fetchPiece[me,me', other,other',s,s'])         //Jogador pega numa peça
	
}


pred stateTransition {
	all s: BoardState, s': state/next[s] | nextState[s,s']
}


pred nextState[ s,s': BoardState]{
	(!endGame[s])//O jogo ja acabou?
	s.currentPlayer = Player1 => 
		play[s.p1Deck,s'.p1Deck, s.p2Deck,s'.p2Deck,s,s']
	else
		play[s.p2Deck,s'.p2Deck, s.p1Deck,s'.p1Deck,s,s']
}

pred endGame[s:BoardState]{
	     s.p1Deck = none || s.p2Deck=none
}

pred gameEnds{
	stateTransition
	endGame[state/last]
}


run {} for exactly 5 Piece, 7 Connection,6 BoardState // testar o estatico
//run stateTransition for exactly 5 Piece, 7 Connection,6 BoardState // testar o dinamico
//run gameEnds for exactly 3 Piece, 7 Connection, 2 BoardState //testar fim do jogo
