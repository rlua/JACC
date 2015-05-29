import java.io.*;
import java.util.StringTokenizer;
import java.util.Vector;
import java.util.Hashtable;

/**
 * @author Rhonald Lua
 * @version 1.3 07/3/2001
 * JACC (Just Another Compiler Compiler) is a YACC-like, parser generator which
 * generates code (in ANSI C, Java, PERL and Python) implementing the LR parsing algorithm.
 * The algorithm is driven by an SLR(1) table constructed from a BNF specification.
 * This program was built around the ideas of chapter 4 of the Dragon Book and parts of Lex & Yacc (by Levine et al).
 */
public class Jacc
{
	final String APPNAME="JACC 1.3";
	final String START="RCLstart";	// auxilliary starting nonterminal symbol
	final String POINTER=".";	// the sentinel pointer/marker/dot
	final String PREFIX="jj";
	final String ERROR="error";	// fictitious error token
	final String EOI="JJEOI";	// end-of-input marker
	String input="";
	String lit="";
	String decl="";
	String trans="";
	String support="";
	String union="";
	String startsym="";
	String filename="input.txt";
	String outputh="";
	String outputc="";
	String trace="";
	int option=1;
	Vector terms=new Vector();	// a vector of strings representing the terminals
	Vector nonterms=new Vector();	// a vector of strings representing the nonterminals
	Vector rules=new Vector();	// a vector of a vector of strings representing the productions;
								// a rule is represented by a vector of strings,
								// with the first element as the lhs, and the arrow or ':' omitted
	Vector semactions=new Vector();	// a vector of strings representing the semantic actions
	Vector LR0=new Vector();	// a vector of a vector of a vector of strings, representing a collection of sets of items
	Vector LR0goto=new Vector();	// a vector of hashtables, implementing the goto transitions for the DFA
	Vector action=new Vector();	// a vector of hashtables, represents the action table
	Vector ruleprec=new Vector();	// a vector of precedences for rules, inherited from the rightmost terminal with an explicit precedence
	Hashtable prec=new Hashtable();	// a map of terminals to precedences
	Hashtable unionmem=new Hashtable();	// a map of terminals to union members
	Vector epsilon=new Vector();	// a vector of symbols which are lhs of epsilon/empty productions

	public static void main (String[] args)
	{
		Jacc jc=new Jacc();

		for(int i=0;i<args.length;i++)
		{
			if(args[i].equals("-c"))
			{
				jc.option=1;
			}
			else if(args[i].equals("-j"))
			{
				jc.option=2;
			}
			else if(args[i].equals("-p"))
			{
				jc.option=4;
			}
			else if(args[i].equals("-y"))
			{
				jc.option=8;
			}
			else
			{
				jc.filename=args[i];
			}
		}
		try
		{
			RandomAccessFile raf=new RandomAccessFile (jc.filename,"r");
			byte[] buf=new byte[(int)raf.length()];
			raf.readFully(buf);
			jc.input=new String(buf);
			raf.close();
		}
		catch(Exception e)
		{
			System.out.print("Error accessing file:"+jc.filename+";"+e.toString()+"\r\n");
		}

		try
		{
			jc.parse();
		}
		catch(Exception e)
		{
			System.out.print(e.toString());
			return;
		}

		if((jc.option & 0x01)>0)
		{
			try
			{
				RandomAccessFile raf=new RandomAccessFile ("j.tab.h.txt","rw");
				raf.writeBytes(jc.outputh);
				raf.close();
			}
			catch(Exception e)
			{
			}
			try
			{
				RandomAccessFile raf=new RandomAccessFile ("j.tab.c.txt","rw");
				raf.writeBytes(jc.outputc);
				raf.close();
			}
			catch(Exception e)
			{
			}
		}
		else if((jc.option & 0x02)>0)
		{
			try
			{
				RandomAccessFile raf=new RandomAccessFile ("jjclass.java.txt","rw");
				raf.writeBytes(jc.outputc);
				raf.close();
			}
			catch(Exception e)
			{
			}
		}
		else if((jc.option & 0x04)>0)
		{
			try
			{
				RandomAccessFile raf=new RandomAccessFile ("jjscript.pl.txt","rw");
				raf.writeBytes(jc.outputc);
				raf.close();
			}
			catch(Exception e)
			{
			}
			try
			{
				RandomAccessFile raf=new RandomAccessFile ("trace.txt","rw");
				raf.writeBytes(jc.trace);
				raf.close();
			}
			catch(Exception e)
			{
			}
		}
		else if((jc.option & 0x08)>0)
		{
			try
			{
				RandomAccessFile raf=new RandomAccessFile ("jjscript.py.txt","rw");
				raf.writeBytes(jc.outputc);
				raf.close();
			}
			catch(Exception e)
			{
			}
			try
			{
				RandomAccessFile raf=new RandomAccessFile ("trace.txt","rw");
				raf.writeBytes(jc.trace);
				raf.close();
			}
			catch(Exception e)
			{
			}
		}
	}

	void preprocess() throws Exception
	{
		int pos,pos2;

		// separate input into declarations, translation rules, and supporting code section
		if((pos=input.indexOf("%%"))==-1)
			throw new Exception("Syntax error; Missing \'%%\'\r\n");
		decl=input.substring(0,pos);
		decl+="\r\n%token "+ERROR+"\r\n";	// add fictitious error token
		decl+="%token "+EOI+"\r\n";	// add end-of-input marker

		if((pos2=input.indexOf("%%",pos+2))==-1)
			throw new Exception("Syntax error; Missing another \'%%\'\r\n");
		trans=input.substring(pos+2,pos2);

		// supporting code section
		support+=input.substring(pos2+2);

		// strip out comments from translation rules section
		while((pos=trans.indexOf("/*"))!=-1)
		{
			if((pos2=trans.indexOf("*/",pos+2))==-1)
				throw new Exception("Syntax error in rules section; Unmatched comment\r\n");
			trans=trans.substring(0,pos)+trans.substring(pos2+2);
		}
		trans=trans.trim();
		if(trans.length()<4)
			throw new Exception("Useless rules section\r\n");
		// add auxilliary start rule
		if(trans.indexOf(":")==-1)
				throw new Exception("Syntax error in rules section; Missing start rule\r\n");
		startsym=trans.substring(0,trans.indexOf(":")).trim();
		trans=START+" : "+startsym+" ; "+trans;

		input="";	// done, release
	}

	void processdecl() throws Exception
	{
		// collect tokens from declarations section
		int i,j;

		// parse literal block
		if((i=decl.indexOf("%{"))!=-1)
		{
			j=decl.indexOf("%}",i+2);
			if(j==-1)
				throw new Exception("Syntax error in declarations section; Unmatched \'%{\'\r\n");
			lit+=decl.substring(i+2,j);
			decl=decl.substring(0,i)+decl.substring(j+2);	// remove literal block from declarations
		}

		// strip out comments
		while((i=decl.indexOf("/*"))!=-1)
		{
			if((j=decl.indexOf("*/",i+2))==-1)
				throw new Exception("Syntax error in declarations section; Unmatched comment\r\n");
			decl=decl.substring(0,i)+decl.substring(j+2);
		}

		i=decl.indexOf("%union");
		if(i!=-1)
		{
			char c;
			i+="%union".length();
			while(true)
			{
				if(i==decl.length())
					throw new Exception("Syntax error in declarations section; %union incomplete\r\n");
				if(decl.charAt(i)=='{')
					break;
				i++;
			}
			int i2=i;
			while(true)
			{
				if(i==decl.length())
					throw new Exception("Syntax error in declarations section; %union incomplete\r\n");
				if(decl.charAt(i)=='}')
					break;
				i++;
			}
			union=decl.substring(i2,i+1);
		}

		i=0;
		StringTokenizer st=new StringTokenizer(decl,"\r\n");
		String um;
		while(st.hasMoreTokens())
		{
			StringTokenizer st2=new StringTokenizer(st.nextToken());
			um=null;
			if(st2.countTokens()>1)
			{
				String t=st2.nextToken();
				if(t.equals("%token"))
				{
					while(st2.hasMoreTokens())
					{
						String t2=st2.nextToken();
						if(t2.charAt(0)=='<')	// <union member>, for terminals
						{
							if(t2.length()<3 || t2.charAt(t2.length()-1)!='>')
								throw new Exception("Syntax error in declarations section\r\n");
							if(um!=null)
								throw new Exception("Syntax error in declarations section\r\n");
							t2=t2.substring(1,t2.length()-1);
							if(union.indexOf(t2)==-1)
								throw new Exception("Error; member not found in union\r\n");
							um=t2;
						}
						else
						{
							if(terms.indexOf(t2)==-1)
								terms.addElement(t2);
							if(um!=null)
							{
								unionmem.put(t2,um);
								um=null;
							}
						}
					}
				}
				else if(t.equals("%type"))
				{
					if(union.equals(""))
						throw new Exception("Error; union declaration missing in declarations section\r\n");
					while(st2.hasMoreTokens())
					{
						String t2=st2.nextToken();
						if(t2.charAt(0)=='<')	// <union member>, for nonterminals
						{
							if(t2.length()<3 || t2.charAt(t2.length()-1)!='>')
								throw new Exception("Syntax error in declarations section\r\n");
							if(um!=null)
								throw new Exception("Syntax error in declarations section\r\n");
							t2=t2.substring(1,t2.length()-1);
							if(union.indexOf(t2)==-1)
								throw new Exception("Error; member not found in union\r\n");
							um=t2;
						}
						else
						{
							if(um!=null)
							{
								unionmem.put(t2,um);
								um=null;
							}
						}
					}
				}
				else if(t.equals("%left"))
				{
					while(st2.hasMoreTokens())
					{
						prec.put(st2.nextToken(),"l"+i);
					}
				}
				else if(t.equals("%right"))
				{
					while(st2.hasMoreTokens())
					{
						prec.put(st2.nextToken(),"r"+i);
					}
				}
				else if(t.equals("%nonassoc"))
				{
					while(st2.hasMoreTokens())
					{
						prec.put(st2.nextToken(),"n"+i);
					}
				}
			}
			i++;
		}
	}

	void processtrans() throws Exception
	{
		int pos=0,pos2;
		int len=trans.length();
		String lhs=null;
		Vector v=null;
		boolean brhs=false;
		int ruleno=-1;
		String tmpprec=null;
		char c;
		while(pos<len)
		{
			c=trans.charAt(pos);
			if(Character.isWhitespace(c))
			{
				pos++;
				continue;
			}
			if(c==':')
			{
				// transition from lhs to rhs
				pos++;
				brhs=true;
				continue;
			}
			if(c=='\'')
			{
				// a literal token
				pos2=pos;
				while(true)
				{
					pos++;
					if(pos>=len)
						throw new Exception("Syntax error; Unmatched \'\r\n");
					c=trans.charAt(pos);
					if(c=='\'')
					{
						pos++;
						if(brhs==false || v==null)
							throw new Exception("Syntax error in lhs\r\n");
						String t=trans.substring(pos2,pos);
						v.addElement(t);
						if(terms.indexOf(t)==-1)
							terms.addElement(t);
						String t2=(String)prec.get(t);
						if(t2!=null)
							tmpprec=t2;
						break;
					}
					else if(c=='\\')	// escape sequence
					{
						pos++;
						if(pos>=len)
							throw new Exception("Syntax error; Unmatched \'\r\n");
					}
				}
				continue;
			}
			if(c=='{')
			{
				// semantic action
				pos2=pos;
				int balance=1;	// count unbalanced braces
				while(true)
				{
					pos++;
					if(pos>=len)
						throw new Exception("Syntax error; Unmatched \'{\'\r\n");
					c=trans.charAt(pos);
					if(c=='{')
					{
						balance++;
					}
					else if(c=='}')
					{
						balance--;
						if(balance<0)
							throw new Exception("Syntax error; Too many \'}\'\r\n");
						if(balance==0)
						{
							pos++;
							if(brhs==false || v==null)
								throw new Exception("Syntax error in lhs\r\n");
							semactions.setElementAt(trans.substring(pos2,pos),ruleno);
							break;
						}
					}
				}
				continue;
			}
			if(c=='|')
			{
				pos++;
				if(brhs==false || v==null)
					throw new Exception("Syntax error in rhs (|)\r\n");
				rules.addElement(v);	// add rule/vector of collected symbols
				if(tmpprec==null)
					tmpprec="";
				ruleprec.addElement(tmpprec);
				tmpprec=null;
				v=new Vector();	// prepare for next rule
				semactions.addElement("");	// prepare for next semantic action
				ruleno++;
				if(lhs==null)
					throw new Exception("Syntax error; Missing lhs\r\n");
				v.addElement(lhs);
				continue;
			}
			if(c==';')
			{
				pos++;
				if(brhs==false || v==null)
					throw new Exception("Syntax error in rhs (;)\r\n");
				rules.addElement(v);	// add rule
				if(v.size()==1)	// if an epsilon production, add to e-list
				{
					if(epsilon.indexOf(lhs)==-1)
						epsilon.addElement(lhs);
				}
				if(tmpprec==null)
					tmpprec="";
				ruleprec.addElement(tmpprec);
				tmpprec=null;
				lhs=null;
				v=null;
				brhs=false;
				continue;
			}
			// form grammar symbol
			pos2=pos;
			while(true)
			{
				pos++;
				if(pos>=len)
					throw new Exception("Syntax error in rhs (gs1)\r\n");
				c=trans.charAt(pos);
				if(Character.isLetterOrDigit(c)==false && c!='_')
				{
					if(brhs)
					{
						// process rhs symbol
						if(v==null)
							throw new Exception("Syntax error in rhs (gs2)\r\n");
						String t=trans.substring(pos2,pos);
						if(t.charAt(0)=='%')
						{
							if(t.equals("%prec"))
							{
								StringTokenizer st=new StringTokenizer(trans.substring(pos));
								if(st.hasMoreTokens())
								{
									String t2=st.nextToken();
									if(Character.isLetterOrDigit(t2.charAt(0)))
									{
										String t3=(String)prec.get(t2);
										if(t3!=null)
											tmpprec=t3;
										pos=trans.indexOf(t2,pos);
										pos+=t2.length();
									}
									else
									{
										throw new Exception("Syntax error in rules section; %prec argument invalid\r\n");
									}
								}
								else
								{
									throw new Exception("Syntax error in rules section; Missing %prec argument\r\n");
								}
							}
							else
							{
								throw new Exception("Syntax error in rules section; Unknown symbol "+t+"\r\n");
							}
						}
						else
						{
							v.addElement(t);
							String t2=(String)prec.get(t);
							if(t2!=null)
								tmpprec=t2;
						}
					}
					else
					{
						// process lhs nonterminal
						v=new Vector();
						lhs=trans.substring(pos2,pos);
						if(nonterms.indexOf(lhs)==-1)
							nonterms.addElement(lhs);
						v.addElement(lhs);
						semactions.addElement("");
						ruleno++;
					}
					break;
				}
			}
		}
	}

	void parse() throws Exception
	{
		preprocess();

		processdecl();

		processtrans();
			System.gc();
		constructCSOI();
			System.gc();
		constructSLR();
			System.gc();
		genCode();
			System.gc();
	}

	void genTrace() throws Exception
	{
		//
		// trace/check/test
		//
		trace+="***productions, semantic actions and precedences\r\n";
		int i,j;
		for(i=0;i<rules.size();i++)
		{
			Vector v=(Vector)rules.elementAt(i);
			for(j=0;j<v.size();j++)
			{
				trace+=(String)v.elementAt(j)+" ";
			}
			trace+="\r\n";
			trace+="\t"+(String)semactions.elementAt(i)+"\r\n";
			trace+="\t"+(String)ruleprec.elementAt(i)+"\r\n";
		}
		trace+="***terminals\r\n";
		for(i=0;i<terms.size();i++)
		{
			trace+=(String)terms.elementAt(i)+"\r\n";
		}
		trace+="***nonterminals\r\n";
		for(i=0;i<nonterms.size();i++)
		{
			trace+=(String)nonterms.elementAt(i)+"\r\n";
		}
		trace+="\r\n***nonterminals which are lhs of epsilon productions\r\n";
		for(i=0;i<epsilon.size();i++)
		{
			trace+=(String)epsilon.elementAt(i)+"\r\n";
		}
		trace+="\r\n***states; sets of items\r\n";
		for(i=0;i<LR0.size();i++)
		{
			Vector v=(Vector)LR0.elementAt(i);
			trace+="	state "+i+"\r\n";
			for(j=0;j<v.size();j++)
			{
				trace+="		";
				Vector v2=(Vector)v.elementAt(j);
				for(int k=0;k<v2.size();k++)
				{
					trace+=(String)v2.elementAt(k)+" ";
				}
				trace+="\r\n";
			}
		}
		trace+="\r\n***DFA transitions\r\n";
		for(i=0;i<LR0goto.size();i++)
		{
			Hashtable ht=(Hashtable)LR0goto.elementAt(i);
			trace+="	state "+i+"\r\n";
			for(j=0;j<terms.size();j++)
			{
				Integer state=(Integer)ht.get(terms.elementAt(j));
				if(state!=null)
				{
					trace+="		"+(String)terms.elementAt(j)+" --> "+state+"\r\n";
				}
			}
			for(j=0;j<nonterms.size();j++)
			{
				Integer state=(Integer)ht.get(nonterms.elementAt(j));
				if(state!=null)
				{
					trace+="		"+(String)nonterms.elementAt(j)+" --> "+state+"\r\n";
				}
			}
		}
		trace+="\r\n***action table\r\n";
		for(i=0;i<action.size();i++)
		{
			Hashtable ht=(Hashtable)action.elementAt(i);
			trace+="	state "+i+"\r\n";
			for(j=0;j<terms.size();j++)
			{
				String act=(String)ht.get(terms.elementAt(j));
				if(act!=null)
				{
					trace+="		"+(String)terms.elementAt(j)+" --> "+act+"\r\n";
				}
			}
		}
/*
		// test
		Vector f;
		String t;
		t=START;
		f=follow(t);
		trace+="\r\n**follow "+t+": ";
		for(i=0;i<f.size();i++)
		{
			trace+=(String)f.elementAt(i)+" ";
		}
*/
//		outputc+="\r\n/**********begin trace**********\r\n\r\n"+trace+"\r\n**********end trace**********/\r\n";
	}

	Vector closure(Vector set1) throws Exception
	{	
		int i,j;
		Vector set=(Vector)set1.clone();
		Vector dirty=new Vector();	// vector of non-kernel items processed
		for(i=0;i<set.size();i++)
		{
			// fetch a single item
			Vector arule=(Vector)set.elementAt(i);
			// look for the 'dot'
			if((j=arule.indexOf(POINTER))==-1)
				throw new Exception("Error; Missing dot in closure\r\n");	// no dot
			if(j+1>=arule.size())
				continue;	// reducible
			String sym=(String)arule.elementAt(j+1);	// symbol after the dot
			if(dirty.indexOf(sym)==-1)
			{
				dirty.addElement(sym);
			}
			else
			{
				continue;
			}
			for(j=0;j<rules.size();j++)
			{
				Vector v=(Vector)((Vector)rules.elementAt(j)).clone();
				if(((String)v.elementAt(0)).equals(sym))
				{
					v.insertElementAt(POINTER,1);
					set.addElement(v);
				}
			}
		}
		//return set.size()>0 ? set : null;
		return set;
	}

	Vector gotoOp(Vector set1, String sym) throws Exception
	{
		Vector set=new Vector();
		for(int i=0;i<set1.size();i++)
		{
			// for each item, find presence of symbol after dot
			Vector v=(Vector)((Vector)set1.elementAt(i)).clone();
			// find dot
			int pos;
			if((pos=v.indexOf(POINTER))==-1)
				throw new Exception("Error; Missing dot in gotoOp\r\n");
			if(pos+1>=v.size())
				continue;	// reducible
			// find symbol
			if(((String)v.elementAt(pos+1)).equals(sym))
			{
				v.removeElementAt(pos);	// move pointer one symbol to the right
				v.insertElementAt(POINTER,pos+1);
				set.addElement(v);
			}
		}

		return (set.size()>0 ? closure(set) : null);
	}

	// return the state if the set of items is already in the collection, -1 otherwise
	int noExist(Vector lr0, Vector set) throws Exception
	{
		int i,j,k,l;
		for(i=0;i<lr0.size();i++)
		{
			// for each set of items
			Vector v=(Vector)lr0.elementAt(i);
			if(v.size()!=set.size())
				continue;
			for(j=0;j<v.size();j++)
			{
				// for each item
				Vector v2=(Vector)v.elementAt(j);
				for(k=0;k<set.size();k++)
				{
					// for each item of set
					Vector vset=(Vector)set.elementAt(k);
					if(vset.size()!=v2.size())
					{
						continue;
					}
					for(l=0;l<vset.size();l++)
					{
						if(v2.elementAt(l).equals(vset.elementAt(l)))
						{
						}
						else
						{
							break;
						}
					}
					if(l==vset.size())
					{
						break;	// item matches
					}
				}
				if(k==set.size())
				{
					break;	// an item does not match
				}
			}
			if(j==v.size())
			{
				break;	// a set of items matches
			}
		}
		return (i==lr0.size() ? -1 : i);	// if i went pass the limit, set not found in lr0
	}

	// construct the collection of sets of items and the goto operation(hashtable)
	void constructCSOI() throws Exception
	{
		int i;
		int istate=0;
		int state;
		// set closure of augmented start rule with dot at left as item 1
		Vector v=new Vector();
		Vector v2=(Vector)((Vector)rules.elementAt(0)).clone();
		v2.insertElementAt(POINTER,1);
		v.addElement(v2);
		LR0.addElement(closure(v));
		LR0goto.addElement(new Hashtable());
		Hashtable ht;
		while(true)
		{
			// compute goto for each grammar symbol
			for(i=0;i<terms.size();i++)
			{
				v=gotoOp((Vector)LR0.elementAt(istate),(String)terms.elementAt(i));
				if(v!=null)
				{
					state=noExist(LR0,v);
					if(state==-1)
					{
						LR0.addElement(v);
						LR0goto.addElement(new Hashtable());
						((Hashtable)LR0goto.elementAt(istate)).put((String)terms.elementAt(i),new Integer(LR0.size()-1));
					}
					else
					{
						((Hashtable)LR0goto.elementAt(istate)).put((String)terms.elementAt(i),new Integer(state));
					}
				}
			}
			for(i=0;i<nonterms.size();i++)
			{
				v=gotoOp((Vector)LR0.elementAt(istate),(String)nonterms.elementAt(i));
				if(v!=null)
				{
					state=noExist(LR0,v);
					if(state==-1)
					{
						LR0.addElement(v);
						LR0goto.addElement(new Hashtable());
						((Hashtable)LR0goto.elementAt(istate)).put((String)nonterms.elementAt(i),new Integer(LR0.size()-1));
					}
					else
					{
						((Hashtable)LR0goto.elementAt(istate)).put((String)nonterms.elementAt(i),new Integer(state));
					}
				}
			}
			istate++;
			if(istate>=LR0.size())
				break;
		}
	}

	// returns a vector of terminals that can follow the symbol in a derivation
	Vector follow(String sym) throws Exception
	{
		Vector f=new Vector();
		if(sym.equals(startsym))
			f.addElement(EOI);	// end-of-input marker is in follow(S)
		int pos,pos2;
		for(int i=0;i<rules.size();i++)
		{
			Vector v=(Vector)rules.elementAt(i);
			// search for sym in rhs
			pos=1;
			while((pos=v.indexOf(sym,pos))!=-1)
			{
				if(pos+1<v.size())
				{
					pos2=pos+1;
					while(pos2<v.size())
					{
						String t=(String)v.elementAt(pos2);
						Vector v2=first(t);
						for(int j=0;j<v2.size();j++)
						{
							String t2=(String)v2.elementAt(j);
							if(f.indexOf(t2)==-1)
								f.addElement(t2);
						}
						//if(epsilon.indexOf(t)==-1)	// if symbol is not an lhs of an epsilon production, stop fetching first() of subsequent symbols
						if(v2.indexOf("")==-1)	// if first(t) does not contain epsilon, stop fetching first() of subsequent symbols
							break;
						pos2++;
					}
					if(pos2==v.size())
					{
						String t=(String)v.elementAt(0);
						if(t.equals(sym)==false)	// if lhs is a different nonterminal from sym, get its follow()
						{
							Vector v3=follow(t);
							for(int j=0;j<v3.size();j++)
							{
								String t2=(String)v3.elementAt(j);
								if(f.indexOf(t2)==-1)
									f.addElement(t2);
							}
						}
					}
				}	// everything that follows the lhs of a rule with sym as the last element is part of follow(sym)
				else if(((String)v.lastElement()).equals(sym))
				{
					String t=(String)v.elementAt(0);
					if(t.equals(sym))	// if same nonterminal, skip, to avoid stack overflow
						break;
					Vector v3=follow(t);
					for(int j=0;j<v3.size();j++)
					{
						String t2=(String)v3.elementAt(j);
						if(f.indexOf(t2)==-1)
							f.addElement(t2);
					}
					break;
				}
				pos++;
			}
		}
		return f;
	}

	Vector first(String sym) throws Exception
	{
		Vector f=new Vector();

		// if a terminal, return it
		if(terms.indexOf(sym)!=-1)
		{
			f.addElement(sym);
			return f;
		}

		// if lhs of an epsilon production, add epsilon ("")
		if(epsilon.indexOf(sym)!=-1)
		{
			f.addElement("");
		}

		for(int i=0;i<rules.size();i++)	// for each rule
		{
			Vector v=(Vector)rules.elementAt(i);
			if(((String)v.elementAt(0)).equals(sym))	// if symbol is an lhs of this rule
			{
				for(int j=1;j<v.size();j++)
				{
					String t=(String)v.elementAt(j);
					if(t.equals(sym))	// if same nonterminal
					{
						// continue searching this rule if current symbol is an lhs of an epsilon production
						if(epsilon.indexOf(t)!=-1)	// TOO RESTRICTIVE: What if t is not epsilon but derives an epsilon?
							continue;
						break;	// if same nonterminal, skip, to avoid stack overflow
					}
					Vector v2=first(t);
					for(int k=0;k<v2.size();k++)
					{
						String t2=(String)v2.elementAt(k);
						if(f.indexOf(t2)==-1)
							f.addElement(t2);
					}
					// stop searching this rule if current symbol is not an lhs of an epsilon production
					//if(epsilon.indexOf(t)==-1)
					if(v2.indexOf("")==-1)	// stop searching this rule if first() of current symbol does not contain epsilon
						break;
				}
			}
		}

		return f;
	}

	// item with dot at right end
	int ruleIndex(Vector item) throws Exception
	{
		int i,j;
		for(i=0;i<rules.size();i++)
		{
			Vector v=(Vector)rules.elementAt(i);
			// match elements before dot with rule
			if(v.size()+1!=item.size())
				continue;
			for(j=0;j<v.size();j++)
			{
				if(((String)v.elementAt(j)).equals((String)item.elementAt(j)))
    			{
				}
				else
				{
					break;
				}
			}
			if(j==v.size())
			{
				break;
			}
		}
		return (i==rules.size() ? -1 : i);
	}

	// construct the SLR(1) parsing table
	void constructSLR() throws Exception
	{
		// construct collection of sets of items: done
		// construct action table
		trace+="***conflicts\r\n";
		for(int i=0;i<LR0.size();i++)	// for each set of items
		{
			action.addElement(new Hashtable());
			Vector v=(Vector)LR0.elementAt(i);
			Hashtable g=(Hashtable)LR0goto.elementAt(i);
			Hashtable a=(Hashtable)action.elementAt(i);
			for(int j=0;j<v.size();j++)	// for each item
			{
				Vector v2=(Vector)v.elementAt(j);
				int pos;
				if((pos=v2.indexOf(POINTER))==-1)
					throw new Exception("Error; Invalid item\r\n");
				if(pos+1<v2.size())
				{
					// shift?
					String t=(String)v2.elementAt(pos+1);
					if(terms.indexOf(t)!=-1)	// if a terminal
					{
						if(g.containsKey(t))	// if a transition exists
						{
							if(a.containsKey(t))	// a possible conflict?
							{
								String t2=(String)a.get(t);
								if(t2.startsWith("r"))
								{
									int irule=Integer.parseInt(t2.substring(1));
									String pr=(String)ruleprec.elementAt(irule);	// get precedence of this rule
									String pt=(String)prec.get(t);	// get precedence of this terminal
									if(pt!=null && pr.length()>0)
									{
										// precedence explicitly specified for both rule and terminal
										int npr=Integer.parseInt(pr.substring(1));
										int npt=Integer.parseInt(pt.substring(1));
										if(npt>npr)
										{
											// shift if terminal has greater precedence than rule
											a.put(t,"s"+g.get(t));
										}
										else if(npt==npr)
										{
											// pt.charAt(0)==pt.charAt(0) should be true
											if(pt.charAt(0)=='r')
											{
												// shift if right associative
												a.put(t,"s"+g.get(t));
											}
										}
									}
									else
									{
										// default, follow rule of thumb
										trace+="shift-reduce conflict, state "+i+", token "+t+"; Choosing to shift\r\n";
										a.put(t,"s"+g.get(t));
									}
								}
								else
								{
									a.put(t,"s"+g.get(t));
								}
							}
							else
							{
								a.put(t,"s"+g.get(t));
							}
						}
					}
				}
				else
				{
					int irule=ruleIndex(v2);	// get rule to which this item corresponds
					if(irule==0)	// i.e. if S' -> S . (should be the first rule) set action[i,EOI] to accept
					{
						a.put(EOI,"a");
						continue;
					}
					if(irule<0)
						throw new Exception("Error; Rule index not found\r\n");
					String pr=(String)ruleprec.elementAt(irule);	// get precedence of this rule
					// reduce?
					Vector f=follow((String)v2.elementAt(0));
					for(int k=0;k<f.size();k++)
					{
						String t=(String)f.elementAt(k);
						if(a.containsKey(t))	// a possible conflict?
						{
							String pt=(String)prec.get(t);	// get precedence of this terminal
							String t2=(String)a.get(t);
							// default
							if(t2.startsWith("s"))
							{
								if(pt!=null && pr.length()>0)
								{
									int npr=Integer.parseInt(pr.substring(1));
									int npt=Integer.parseInt(pt.substring(1));
									if(npr>npt)
									{
										// reduce if rule has greater precedence than terminal
										a.put(t,"r"+irule);
									}
									else if(npt==npr)
									{
										// pt.charAt(0)==pt.charAt(0) should be true
										if(pt.charAt(0)=='l')
										{
											// reduce if left associative
											a.put(t,"r"+irule);
										}
									}
								}
								else
								{
									trace+="shift-reduce conflict, state "+i+", token "+t+"; Choosing not to reduce\r\n";
								}
							}
							else if(t2.startsWith("r"))
							{
								int irule2=Integer.parseInt(t2.substring(1));
								String pr2=(String)ruleprec.elementAt(irule2);
								if(pr.length()>0 && pr2.length()>0)
								{
									int npr=Integer.parseInt(pr.substring(1));
									int npr2=Integer.parseInt(pr2.substring(1));
									if(npr>npr2)
									{
										// reduce if rule has greater precedence than terminal
										a.put(t,"r"+irule);
									}
									else if(npr==npr2)
									{
										// apply default, associativity types don't seem to matter
										if(irule2>irule)
										{
											a.put(t,"r"+irule);
										}
									}
								}
								else
								{
									trace+="reduce-reduce conflict, state "+i+", token "+t+"; Choosing to reduce with the topmost rule\r\n";
									if(irule2>irule)
									{
										a.put(t,"r"+irule);
									}
								}
							}
							else
							{
								a.put(t,"r"+irule);
							}
						}
						else
						{
							a.put(t,"r"+irule);
						}
					}
				}
			}
		}
		trace+="\r\n";
	}

/////////////////////////////////////// ANSI C ///////////////////////////////////////

	// replace the $n's, etc. in { ... }
	String parseSemaction(String s, int ruleno)	throws Exception
	{
		Vector v=(Vector)rules.elementAt(ruleno);
		int rhslen=v.size()-1;

		String so="{";

		if(s.length()<1)
		{
			return " vstackptr-="+(rhslen-1)+";";
			/*
			epsilon production contains this case:
			return " vstackptr++;";
			and stack value is indeterminate
			*/
		}

		int pos=1,pos2=1,len=s.length();	// skip '{'
		char c;
		if(rhslen>0)
			so+="memcpy(&rclval,&vstack[vstackptr-"+(rhslen-1)+"],sizeof(JJSTYPE));\r\n";
		else	// if an epsilon production
			so+="memset(&rclval,0,sizeof(JJSTYPE));\r\n";
		while(pos<len-1)
		{
			c=s.charAt(pos);
			if(Character.isWhitespace(c))	// skip whitespace
			{
				pos++;
				continue;
			}
			if(c=='\"')	// skip string literal
			{
				pos++;
				while(s.charAt(pos)!='\"')
				{
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					if(s.charAt(pos)=='\\')	// escape sequence
					{
						pos++;
						if(pos>=len-1)
							throw new Exception("Syntax error in semantic action section\r\n");
					}
					pos++;
				}
				pos++;
				continue;
			}
			if(c=='\'')	// skip character literal
			{
				pos++;
				while(s.charAt(pos)!='\'')
				{
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					if(s.charAt(pos)=='\\')	// escape sequence
					{
						pos++;
						if(pos>=len-1)
							throw new Exception("Syntax error in semantic action section\r\n");
					}
					pos++;
				}
				pos++;
				continue;
			}
			if(c=='/')
			{
				pos++;
				if(pos>=len-1)
					throw new Exception("Syntax error in semantic action section\r\n");
				if(s.charAt(pos)=='*')
				{
					pos++;
					// comment begins
					if((pos=s.indexOf("*/",pos))==-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					pos+=2;
				}
				continue;
			}
			if(c=='$')
			{
				pos++;
				if(pos>=len-1)
					throw new Exception("Syntax error in semantic action section\r\n");
				if(s.charAt(pos)=='$')
				{
					so+=s.substring(pos2,pos-1);
					so+="rclval";
					String m=(String)unionmem.get((String)v.elementAt(0));
					if(m!=null)
						so+="."+m;
					pos++;
					pos2=pos;
					continue;
				}
				if(Character.isDigit(s.charAt(pos)))
				{
					so+=s.substring(pos2,pos-1);
					pos2=pos++;
					while(Character.isDigit(s.charAt(pos)))
					{
						pos++;
					}
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					int idx=Integer.parseInt(s.substring(pos2,pos));
					if(idx>rhslen || idx<1)
						throw new Exception("Error in semantic action section, index out of range\r\n");
					so+="vstack[vstackptr-"+(rhslen-idx)+"]";
					String m=(String)unionmem.get((String)v.elementAt(idx));
					if(m!=null)
						so+="."+m;
					pos2=pos;
					continue;
				}
				pos++;
				continue;
			}
			pos++;
		}
		so+=s.substring(pos2,pos);
		so+="\r\n";
		so+="	memcpy(&vstack[vstackptr-="+(rhslen-1)+"],&rclval,sizeof(JJSTYPE));\r\n";
		/*
		epsilon production contains this case:
		so+="	memcpy(&vstack[++vstackptr],&rclval,sizeof(JJSTYPE));\r\n";
		*/
		so+="	}\r\n";
		return so;
	}

	// write ANSI C-code implementation
	void genANSICCode() throws Exception
	{
		int i,j;

		// header

		outputh+="/*\r\n"+APPNAME+"generated header file, by Rhonald C. Lua.  (C) 2000 All rights reserved.\r\n*/\r\n";
		// literal block
		outputh+="\r\n/*start of literal block*/\r\n";
		outputh+=lit;
		outputh+="/*end of literal block*/\r\n";
		outputh+="\r\n";
		outputh+="#include <stdio.h>\r\n";
		outputh+="#include <string.h>\r\n";
		outputh+="\r\n";
		if(union.length()>0)
		{
			outputh+="typedef union "+union+" JJSTYPE;\r\n";
		}
		else
		{
			outputh+="#ifndef JJSTYPE\r\n";
			outputh+="#define JJSTYPE int\r\n";
			outputh+="#endif\r\n";
		}
		outputh+="\r\n";
		outputh+="#ifndef JJSDEPTH\r\n";
		outputh+="#define JJSDEPTH 256\r\n";
		outputh+="#endif\r\n";
		outputh+="\r\n";
		outputh+="typedef struct { int inst,param; } ACTION_T;\r\n";
		outputh+="typedef struct { int nonterm,numsyms; } RULE_T;\r\n";
		outputh+="\r\n";
		outputh+="#define NUMTERMS "+terms.size()+"\r\n";
		outputh+="#define NUMNONTERMS "+nonterms.size()+"\r\n";
		outputh+="#define NUMRULES "+rules.size()+"\r\n";
		outputh+="#define NUMSTATES "+LR0.size()+"\r\n";
		outputh+="#define INST_ERROR -1\r\n";
		outputh+="#define INST_SHIFT 0\r\n";
		outputh+="#define INST_REDUCE 1\r\n";
		outputh+="#define INST_ACCEPT 2\r\n";

		// source
		outputc+="/*\r\n"+APPNAME+" generated source file, by Rhonald C. Lua.  (C) 2000 All rights reserved.\r\n";
		outputc+="Notes:\r\n\tYou must provide an implementation of the lexer \'int "+PREFIX+"lex()\'\r\n";
		outputc+="\twhich returns a token code with ASCII values for character literals and #define constants for other terminals\r\n";
		outputc+="*/\r\n";
		outputc+="#include \"j.tab.h\"\r\n";
		outputc+="\r\n";
		outputc+="JJSTYPE "+PREFIX+"lval;\r\n";
		outputc+="int "+PREFIX+"lex();\r\n";
		outputc+="JJSTYPE vstack[JJSDEPTH];\r\n";
		outputc+="int vstackptr;\r\n";
		outputc+="void "+PREFIX+"error(char* errmsg);\r\n";

		// build terminal map
		// insertion sort the terminals for faster mapping
		/*
		for(i=1;i<terms.size();i++)
		{
			j=i;
			String tmp=(String)terms.elementAt(j);
			int aval=256;
			if(tmp.charAt(0)=='\'')
			{
				aval=Character.digit(tmp.charAt(1),10);
			}
			while(j>0)
			{
				String tmp2=(String)terms.elementAt(j-1);
				int aval2=256;
				if(tmp2.charAt(0)=='\'')
				{
					aval2=Character.digit(tmp2.charAt(1),10);
				}
				if( aval >  aval2 )
					break;
				// shift up
				terms.setElementAt((String)terms.elementAt(j-1),j);
				j--;
			}
			terms.setElementAt(tmp,j);
		}
		*/
		outputc+="\r\n";
		outputc+="const int termmap[NUMTERMS]=\r\n{\r\n";
		for(i=0;i<terms.size();i++)
		{
			String t=(String)terms.elementAt(i);
			if(t.startsWith("\'")==false)
				outputh+="#define "+t+" "+(256+i)+"\r\n";
			outputc+=t+",\r\n";
		}
		outputc+="};\r\n";

		// build rules array
		outputc+="\r\n";
		outputc+="const RULE_T rules[NUMRULES]=\r\n{\r\n";
		for(i=0;i<rules.size();i++)
		{
			Vector v=(Vector)rules.elementAt(i);
			int inonterm=nonterms.indexOf((String)v.elementAt(0));
			if(inonterm==-1)
				throw new Exception("Error; lhs not in nonterminal vector\r\n");
			outputc+="{ "+inonterm+","+(v.size()-1)+" },\r\n";
		}
		outputc+="};\r\n";

		// build action table
		outputc+="\r\n";
		outputc+="const ACTION_T action[NUMSTATES][NUMTERMS]=\r\n{\r\n";
		for(i=0;i<action.size();i++)
		{
			Hashtable ht=(Hashtable)action.elementAt(i);
			outputc+="{";
			for(j=0;j<terms.size();j++)
			{
				String t=(String)terms.elementAt(j);
				if(ht.containsKey(t))
				{
					String t2=(String)ht.get(t);
					if(t2.startsWith("s"))
					{
						// shift
						outputc+="{ INST_SHIFT,"+t2.substring(1)+"},";
					}
					else if(t2.startsWith("r"))
					{
						// reduce
						outputc+="{ INST_REDUCE,"+t2.substring(1)+"},";
					}
					else if(t2.startsWith("a"))
					{
						// accept
						outputc+="{ INST_ACCEPT,0 },";
					}
					else
					{
						// error
						outputc+="{ INST_ERROR,0 },";
					}
				}
				else
				{
					// error
					outputc+="{ INST_ERROR,0 },";
				}
			}
			outputc+=" },\r\n";
		}
		outputc+="};\r\n";

		// build goto table
		outputc+="\r\n";
		outputc+="const int gototab[NUMSTATES][NUMNONTERMS]=\r\n{\r\n";
		for(i=0;i<LR0goto.size();i++)
		{
			Hashtable ht=(Hashtable)LR0goto.elementAt(i);
			outputc+="{";
			for(j=0;j<nonterms.size();j++)
			{
				String t=(String)nonterms.elementAt(j);
				if(ht.containsKey(t))
				{
					outputc+=ht.get(t)+",";
				}
				else
				{
					outputc+="-1,";
				}
			}
			outputc+="},\r\n";
		}
		outputc+="};\r\n";

		// build semantic actions functions
		outputc+="\r\n";
		outputc+="void semactions(int r)\r\n";
		outputc+="{\r\n";
		outputc+="	JJSTYPE rclval;\r\n";
		outputc+="	switch(r)\r\n";
		outputc+="	{\r\n";
		for(i=0;i<semactions.size();i++)
		{
			String t=(String)semactions.elementAt(i);
			outputc+="/*\r\n"+t+"\r\n*/\r\n";
			outputc+="	case "+i+":"+parseSemaction(t,i)+"break;\r\n";
		}
		outputc+="	}\r\n";
		outputc+="}\r\n";

		outputc+="\r\n";
		outputc+="void "+PREFIX+"error(char* errmsg)\r\n";
		outputc+="{\r\n";
		outputc+="	fprintf(stderr,\"%s\\n\",errmsg);\r\n";
		outputc+="}\r\n";

		outputc+="\r\n";
		outputc+="int maptoken(int c)\r\n";
		outputc+="{\r\n";
		outputc+="	int i;\r\n";
		outputc+="	for(i=0;i<NUMTERMS;i++)\r\n";
		outputc+="	{\r\n";
		outputc+="		if(termmap[i]==c)\r\n";
		outputc+="			return i;\r\n";
		outputc+="	}\r\n";
		outputc+="	return -1;\r\n";
		outputc+="}\r\n";
		outputc+="\r\n";
		outputc+="int stack[JJSDEPTH];\r\n";
		outputc+="int stackptr;\r\n";
		outputc+="\r\n";
		outputc+="int "+PREFIX+"parse()\r\n";
		outputc+="{\r\n";
		outputc+="	int c="+PREFIX+"lex();\r\n";
		outputc+="	int ic,s,inst,param,tmp;\r\n";
		outputc+="	stackptr=0;\r\n";
		outputc+="	vstackptr=0;\r\n";
		outputc+="	stack[stackptr]=0;\r\n";
		outputc+="	memcpy(&vstack[vstackptr],&"+PREFIX+"lval,sizeof(JJSTYPE));\r\n";
		outputc+="	while(1)\r\n";
		outputc+="	{\r\n";
		outputc+="		ic=maptoken(c);\r\n";
		outputc+="		if(ic<0)\r\n";
		outputc+="		{\r\n";
		outputc+="			inst=INST_ERROR;\r\n";
		outputc+="		}\r\n";
		outputc+="		else\r\n";
		outputc+="		{\r\n";
		outputc+="			s=stack[stackptr];\r\n";
		outputc+="			inst=action[s][ic].inst;\r\n";
		outputc+="			param=action[s][ic].param;\r\n";
		outputc+="		}\r\n";
		outputc+="		if(inst==INST_SHIFT)\r\n";
		outputc+="		{\r\n";
		outputc+="			if(stackptr+2>=JJSDEPTH)	{	"+PREFIX+"error(\"error, stack overflow\\r\\n\");	break;	}\r\n";
		outputc+="			stack[++stackptr]=ic;\r\n";
		outputc+="			stack[++stackptr]=param;\r\n";
		outputc+="			c="+PREFIX+"lex();\r\n";
		outputc+="			if(vstackptr+1>=JJSDEPTH)	{	"+PREFIX+"error(\"error, value stack overflow\\r\\n\");	break;	}\r\n";
		outputc+="			memcpy(&vstack[++vstackptr],&"+PREFIX+"lval,sizeof(JJSTYPE));\r\n";
		outputc+="		}\r\n";
		outputc+="		else if(inst==INST_REDUCE)\r\n";
		outputc+="		{\r\n";
		outputc+="			stackptr-=2*rules[param].numsyms;\r\n";
		outputc+="			if(stackptr<0)	{	"+PREFIX+"error(\"error, stack underflow\\r\\n\");	break;	}\r\n";
		outputc+="			tmp=gototab[stack[stackptr]][rules[param].nonterm];\r\n";
		outputc+="			stack[++stackptr]=rules[param].nonterm;\r\n";
		outputc+="			if(tmp<0)	{	"+PREFIX+"error(\"error in gototab\\r\\n\");	break;	}\r\n";
		outputc+="			stack[++stackptr]=tmp;\r\n";
		outputc+="			memcpy(&"+PREFIX+"lval,&vstack[vstackptr--],sizeof(JJSTYPE));\r\n";/*temporarily remove value of recently shifted token*/
		outputc+="			semactions(param);\r\n";
		outputc+="			memcpy(&vstack[++vstackptr],&"+PREFIX+"lval,sizeof(JJSTYPE));\r\n";
		outputc+="		}\r\n";
		outputc+="		else if(inst==INST_ACCEPT)\r\n";
		outputc+="		{\r\n";
		outputc+="			break;\r\n";
		outputc+="		}\r\n";
		outputc+="		else\r\n";
		outputc+="		{\r\n";
		outputc+="			tmp=0;\r\n";
		outputc+="			ic=maptoken(error);\r\n";
		outputc+="			while(1)\r\n";
		outputc+="			{\r\n";
		outputc+="				stackptr-=2;\r\n";
		outputc+="				if(stackptr<0)	{	tmp=1; break;	}\r\n";
		outputc+="				s=stack[stackptr];\r\n";
		outputc+="				inst=action[s][ic].inst;\r\n";
		outputc+="				param=action[s][ic].param;\r\n";
		outputc+="				if(inst==INST_SHIFT)\r\n";
		outputc+="				{\r\n";
		outputc+="					if(stackptr+2>=JJSDEPTH)	{	tmp=1; "+PREFIX+"error(\"error, stack overflow\\r\\n\");	break;	}\r\n";
		outputc+="					stack[++stackptr]=ic;\r\n";
		outputc+="					stack[++stackptr]=param;\r\n";
		outputc+="					c="+PREFIX+"lex();\r\n";
		outputc+="					if(vstackptr+1>=JJSDEPTH)	{	tmp=1; "+PREFIX+"error(\"error, value stack overflow\\r\\n\");	break;	}\r\n";
		outputc+="					memcpy(&vstack[++vstackptr],&"+PREFIX+"lval,sizeof(JJSTYPE));\r\n";
		outputc+="					break;\r\n";
		outputc+="				}\r\n";
		outputc+="			}\r\n";
		outputc+="			if(tmp)	{	"+PREFIX+"error(\"error!\\r\\n\");	break;	}\r\n";
		outputc+="		}\r\n";
		outputc+="	}\r\n";
		outputc+="	return 0;\r\n";
		outputc+="}\r\n";

		outputc+="\r\n/*supporting code*/\r\n"+support;
	}

/////////////////////////////////////// JAVA ///////////////////////////////////////

	// replace the $n's, etc. in { ... }
	String parseSemaction2(String s, int ruleno)	throws Exception
	{
		Vector v=(Vector)rules.elementAt(ruleno);
		int rhslen=v.size()-1;

		String so="{";

		if(s.length()<1)
		{
			if(rhslen>1)
				return "for(int rcli=0;rcli<"+(rhslen-1)+";rcli++) vstack.pop(); ";
			else if(rhslen==1)
				return " ";	// no use to pop
			else	// if an epsilon production, push dummy value
				return "vstack.push(new Integer(0)); ";
		}

		int pos=1,pos2=1,len=s.length();	// skip '{'
		char c;
		if(rhslen>0)
			so+="rclval=vstack.elementAt(vstack.size()-1-"+(rhslen-1)+");\r\n";
		else
			so+="rclval=new Integer(0);\r\n";
		while(pos<len-1)
		{
			c=s.charAt(pos);
			if(Character.isWhitespace(c))	// skip whitespace
			{
				pos++;
				continue;
			}
			if(c=='\"')	// skip string literal
			{
				pos++;
				while(s.charAt(pos)!='\"')
				{
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					if(s.charAt(pos)=='\\')	// escape sequence
					{
						pos++;
						if(pos>=len-1)
							throw new Exception("Syntax error in semantic action section\r\n");
					}
					pos++;
				}
				pos++;
				continue;
			}
			if(c=='\'')	// skip character literal
			{
				pos++;
				while(s.charAt(pos)!='\'')
				{
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					if(s.charAt(pos)=='\\')	// escape sequence
					{
						pos++;
						if(pos>=len-1)
							throw new Exception("Syntax error in semantic action section\r\n");
					}
					pos++;
				}
				pos++;
				continue;
			}
			if(c=='/')
			{
				pos++;
				if(pos>=len-1)
					throw new Exception("Syntax error in semantic action section\r\n");
				if(s.charAt(pos)=='*')
				{
					pos++;
					// comment begins
					if((pos=s.indexOf("*/",pos))==-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					pos+=2;
				}
				continue;
			}
			if(c=='$')
			{
				pos++;
				if(pos>=len-1)
					throw new Exception("Syntax error in semantic action section\r\n");
				if(s.charAt(pos)=='$')
				{
					so+=s.substring(pos2,pos-1);
					so+="rclval";
					//String m=(String)unionmem.get((String)v.elementAt(0));
					//if(m!=null)
					//	so+="."+m;
					pos++;
					pos2=pos;
					continue;
				}
				if(Character.isDigit(s.charAt(pos)))
				{
					so+=s.substring(pos2,pos-1);
					pos2=pos++;
					while(Character.isDigit(s.charAt(pos)))
					{
						pos++;
					}
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					int idx=Integer.parseInt(s.substring(pos2,pos));
					if(idx>rhslen || idx<1)
						throw new Exception("Error in semantic action section, index out of range\r\n");
					so+="vstack.elementAt(vstack.size()-1-"+(rhslen-idx)+")";
					//String m=(String)unionmem.get((String)v.elementAt(idx));
					//if(m!=null)
					//	so+="."+m;
					pos2=pos;
					continue;
				}
				pos++;
				continue;
			}
			pos++;
		}
		so+=s.substring(pos2,pos);
		so+="\r\n";
		so+="	for(int rclj=0;rclj<"+rhslen+";rclj++) vstack.pop();\r\n\tvstack.push(rclval);\r\n";
		so+="	}\r\n";
		return so;
	}

	// write Java class implementation
	void genJavaCode() throws Exception
	{
		int i,j;

		outputc+="/*\r\n"+APPNAME+" generated file, by Rhonald C. Lua.  (C) 2000 All rights reserved.\r\n";
		outputc+="Notes:\r\n\tYou must provide an implementation of the lexer \'String "+PREFIX+"lex()\'\r\n";
		outputc+="\twhich returns a token code in the format \'<char>\' for character literals and the symbol name for other terminals\r\n";
		outputc+="*/\r\n";
		// literal block
		outputc+="\r\n/*start of literal block*/\r\n";
		outputc+=lit;
		outputc+="/*end of literal block*/\r\n\r\n";
		outputc+="import java.util.Stack;\r\n";
		outputc+="import java.util.Hashtable;\r\n\r\n";
		outputc+="public class "+PREFIX+"class\r\n{\r\n";
		outputc+="final int NUMTERMS="+terms.size()+";\r\n";
		outputc+="final int NUMNONTERMS="+nonterms.size()+";\r\n";
		outputc+="final int NUMRULES="+rules.size()+";\r\n";
		outputc+="final int NUMSTATES="+LR0.size()+";\r\n";
		outputc+="final int INST_ERROR=-1;\r\n";
		outputc+="final int INST_SHIFT=0;\r\n";
		outputc+="final int INST_REDUCE=1;\r\n";
		outputc+="final int INST_ACCEPT=2;\r\n";

		outputc+="\r\n";
		outputc+="Object "+PREFIX+"lval;\r\n";
		outputc+="Stack vstack;\r\n";
		outputc+="Stack stack;\r\n";

		// build terminal map
		outputc+="\r\n";
		outputc+="Hashtable termmap=new Hashtable();\r\n";
		outputc+=""+PREFIX+"class()\r\n{\r\n";
		for(i=0;i<terms.size();i++)
		{
			outputc+="\ttermmap.put(\""+(String)terms.elementAt(i)+"\",new Integer("+i+"));\r\n";
		}
		outputc+="}\r\n";

		// build rules array
		outputc+="\r\n";
		outputc+="final int rules[][]=\r\n{\r\n";
		for(i=0;i<rules.size();i++)
		{
			Vector v=(Vector)rules.elementAt(i);
			int inonterm=nonterms.indexOf((String)v.elementAt(0));
			if(inonterm==-1)
				throw new Exception("Error; lhs not in nonterminal vector\r\n");
			outputc+="{ "+inonterm+","+(v.size()-1)+" },\r\n";
		}
		outputc+="};\r\n";

		// build action table
		outputc+="\r\n";
		outputc+="final int action[][][]=\r\n{\r\n";
		for(i=0;i<action.size();i++)
		{
			Hashtable ht=(Hashtable)action.elementAt(i);
			outputc+="{";
			for(j=0;j<terms.size();j++)
			{
				String t=(String)terms.elementAt(j);
				if(ht.containsKey(t))
				{
					String t2=(String)ht.get(t);
					if(t2.startsWith("s"))
					{
						// shift
						outputc+="{ INST_SHIFT,"+t2.substring(1)+"},";
					}
					else if(t2.startsWith("r"))
					{
						// reduce
						outputc+="{ INST_REDUCE,"+t2.substring(1)+"},";
					}
					else if(t2.startsWith("a"))
					{
						// accept
						outputc+="{ INST_ACCEPT,0 },";
					}
					else
					{
						// error
						outputc+="{ INST_ERROR,0 },";
					}
				}
				else
				{
					// error
					outputc+="{ INST_ERROR,0 },";
				}
			}
			outputc+=" },\r\n";
		}
		outputc+="};\r\n";

		// build goto table
		outputc+="\r\n";
		outputc+="final int gototab[][]=\r\n{\r\n";
		for(i=0;i<LR0goto.size();i++)
		{
			Hashtable ht=(Hashtable)LR0goto.elementAt(i);
			outputc+="{";
			for(j=0;j<nonterms.size();j++)
			{
				String t=(String)nonterms.elementAt(j);
				if(ht.containsKey(t))
				{
					outputc+=ht.get(t)+",";
				}
				else
				{
					outputc+="-1,";
				}
			}
			outputc+="},\r\n";
		}
		outputc+="};\r\n";

		// build semantic actions functions
		outputc+="\r\n";
		outputc+="void semactions(int r) throws Exception\r\n";
		outputc+="{\r\n";
		outputc+="	Object rclval;\r\n";
		outputc+="	switch(r)\r\n";
		outputc+="	{\r\n";
		for(i=0;i<semactions.size();i++)
		{
			String t=(String)semactions.elementAt(i);
			outputc+="	case "+i+":"+parseSemaction2(t,i)+"break;\r\n";
		}
		outputc+="	}\r\n";
		outputc+="}\r\n";

		outputc+="\r\n";
		outputc+="void "+PREFIX+"error(String errmsg) throws Exception\r\n";
		outputc+="{\r\n";
		outputc+="\tthrow new Exception(errmsg);\r\n";
		outputc+="}\r\n";

		outputc+="\r\n";
		outputc+="int "+PREFIX+"parse() throws Exception\r\n";
		outputc+="{\r\n";
		outputc+="	String c="+PREFIX+"lex();\r\n";
		outputc+="	int ic,itmp,s,inst,param=0;\r\n";
		outputc+="	Object tmp;\r\n";
		outputc+="	stack=new Stack();\r\n";
		outputc+="	stack.push(new Integer(0));\r\n";
		outputc+="	vstack=new Stack();\r\n";
		outputc+="	vstack.push("+PREFIX+"lval);\r\n";
		outputc+="	while(true)\r\n";
		outputc+="	{\r\n";
		outputc+="		tmp=termmap.get(c);\r\n";
		outputc+="		if(tmp==null)\r\n";
		outputc+="		{\r\n";
		outputc+="			inst=INST_ERROR;\r\n";
		outputc+="		}\r\n";
		outputc+="		else\r\n";
		outputc+="		{\r\n";
		outputc+="			s=((Integer)stack.peek()).intValue();\r\n";
		outputc+="			ic=((Integer)tmp).intValue();\r\n";
		outputc+="			inst=action[s][ic][0];\r\n";
		outputc+="			param=action[s][ic][1];\r\n";
		outputc+="		}\r\n";
		outputc+="		if(inst==INST_SHIFT)\r\n";
		outputc+="		{\r\n";
		outputc+="			stack.push(new Integer(param));\r\n";
		outputc+="			c="+PREFIX+"lex();\r\n";
		outputc+="			vstack.push("+PREFIX+"lval);\r\n";
		outputc+="		}\r\n";
		outputc+="		else if(inst==INST_REDUCE)\r\n";
		outputc+="		{\r\n";
		outputc+="			for(int i=0;i<rules[param][1];i++) stack.pop();\r\n";
		outputc+="			itmp=gototab[((Integer)stack.peek()).intValue()][rules[param][0]];\r\n";
		outputc+="			if(itmp<0)	{	"+PREFIX+"error(\"error in gototab\\r\\n\");	break;	}\r\n";
		outputc+="			stack.push(new Integer(itmp));\r\n";
		outputc+="			"+PREFIX+"lval=vstack.pop();\r\n";/*temporarily remove value of recently shifted token*/
		outputc+="			semactions(param);\r\n";
		outputc+="			vstack.push("+PREFIX+"lval);\r\n";
		outputc+="		}\r\n";
		outputc+="		else if(inst==INST_ACCEPT)\r\n";
		outputc+="		{\r\n";
		outputc+="			break;\r\n";
		outputc+="		}\r\n";
		outputc+="		else\r\n";
		outputc+="		{\r\n";
		outputc+="			ic=((Integer)termmap.get(\""+ERROR+"\")).intValue();\r\n";
		outputc+="			itmp=0;\r\n";
		outputc+="			while(true)\r\n";
		outputc+="			{\r\n";
		outputc+="				if(stack.empty()) { itmp=1; break; }\r\n";
		outputc+="				s=((Integer)stack.pop()).intValue();\r\n";
		outputc+="				inst=action[s][ic][0];\r\n";
		outputc+="				param=action[s][ic][1];\r\n";
		outputc+="				if(inst==INST_SHIFT)\r\n";
		outputc+="				{\r\n";
		outputc+="					stack.push(new Integer(param));\r\n";
		outputc+="					c="+PREFIX+"lex();\r\n";
		outputc+="					vstack.push("+PREFIX+"lval);\r\n";
		outputc+="					break;\r\n";
		outputc+="				}\r\n";
		outputc+="			}\r\n";
		outputc+="			if(itmp==1) { "+PREFIX+"error(\"error!\\r\\n\"); break; }\r\n";
		outputc+="		}\r\n";
		outputc+="	}\r\n";
		outputc+="	return 0;\r\n";
		outputc+="}\r\n";

		outputc+="\r\n/*supporting code*/\r\n"+support+"\r\n}//end "+PREFIX+"class\r\n";
	}

/////////////////////////////////////// PERL ///////////////////////////////////////

	// replace the $n's, etc. in { ... }
	String parseSemaction3(String s, int ruleno)	throws Exception
	{
		Vector v=(Vector)rules.elementAt(ruleno);
		int rhslen=v.size()-1;

		String so="{";

		if(s.length()<1)
		{
			return " $#vstack-="+(rhslen-1)+";";
			/*
			epsilon production contains this case:
			return " $#vstack++;";
			and stack value is indeterminate
			*/
		}

		int pos=1,pos2=1,len=s.length();	// skip '{'
		char c;
		if(rhslen>0)
			so+="$rclval=$vstack[$#vstack-"+(rhslen-1)+"];\r\n";
		else	// if an epsilon production
			so+="$rclval=0;\r\n";
		while(pos<len-1)
		{
			c=s.charAt(pos);
			if(Character.isWhitespace(c))	// skip whitespace
			{
				pos++;
				continue;
			}
			if(c=='\"')	// skip string literal
			{
				pos++;
				while(s.charAt(pos)!='\"')
				{
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					if(s.charAt(pos)=='\\')	// escape sequence
					{
						pos++;
						if(pos>=len-1)
							throw new Exception("Syntax error in semantic action section\r\n");
					}
					pos++;
				}
				pos++;
				continue;
			}
			if(c=='\'')	// skip character literal
			{
				pos++;
				while(s.charAt(pos)!='\'')
				{
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					if(s.charAt(pos)=='\\')	// escape sequence
					{
						pos++;
						if(pos>=len-1)
							throw new Exception("Syntax error in semantic action section\r\n");
					}
					pos++;
				}
				pos++;
				continue;
			}
			if(c=='/')
			{
				pos++;
				if(pos>=len-1)
					throw new Exception("Syntax error in semantic action section\r\n");
				if(s.charAt(pos)=='*')
				{
					pos++;
					// comment begins
					if((pos=s.indexOf("*/",pos))==-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					pos+=2;
				}
				continue;
			}
			if(c=='$')
			{
				pos++;
				if(pos>=len-1)
					throw new Exception("Syntax error in semantic action section\r\n");
				if(s.charAt(pos)=='$')
				{
					so+=s.substring(pos2,pos-1);
					so+="$rclval";
					//String m=(String)unionmem.get((String)v.elementAt(0));
					//if(m!=null)
					//	so+="."+m;
					pos++;
					pos2=pos;
					continue;
				}
				if(Character.isDigit(s.charAt(pos)))
				{
					so+=s.substring(pos2,pos-1);
					pos2=pos++;
					while(Character.isDigit(s.charAt(pos)))
					{
						pos++;
					}
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					int idx=Integer.parseInt(s.substring(pos2,pos));
					if(idx>rhslen || idx<1)
						throw new Exception("Error in semantic action section, index out of range\r\n");
					so+="$vstack[$#vstack-"+(rhslen-idx)+"]";
					//String m=(String)unionmem.get((String)v.elementAt(idx));
					//if(m!=null)
					//	so+="."+m;
					pos2=pos;
					continue;
				}
				pos++;
				continue;
			}
			pos++;
		}
		so+=s.substring(pos2,pos);
		so+="\r\n";
		so+="	$vstack[$#vstack-="+(rhslen-1)+"]=$rclval;\r\n";
		/*
		epsilon production contains this case:
		so+="	vstack[++$#vstack]=rclval;\r\n";
		*/
		so+="	}\r\n";
		return so;
	}

	// write PERL code implementation
	void genPERLCode() throws Exception
	{
		int i,j;

		outputc+="#"+APPNAME+" generated source file, by Rhonald C. Lua.  (C) 2000 All rights reserved.\r\n";
		outputc+="#Notes:\r\n#You must provide an implementation of the lexer \'sub "+PREFIX+"lex()\'\r\n";
		outputc+="#which returns a token code in the format \'<char>\' for character literals and the symbol name for other terminals\r\n";
		outputc+="\r\n#start of literal block\r\n";
		outputc+=lit;
		outputc+="#end of literal block\r\n\r\n";
		outputc+="my $NUMTERMS="+terms.size()+";\r\n";
		outputc+="my $NUMNONTERMS="+nonterms.size()+";\r\n";
		outputc+="my $NUMRULES="+rules.size()+";\r\n";
		outputc+="my $NUMSTATES="+LR0.size()+";\r\n";
		outputc+="my $INST_ERROR=-1;\r\n";
		outputc+="my $INST_SHIFT=0;\r\n";
		outputc+="my $INST_REDUCE=1;\r\n";
		outputc+="my $INST_ACCEPT=2;\r\n";

		outputc+="\r\n";
		outputc+="my $jjlval;\r\n";
		outputc+="my @stack;\r\n";
		outputc+="my @vstack;\r\n";

		// build terminal map
		outputc+="\r\n";
		outputc+="my %termmap=\r\n(\r\n";
		for(i=0;i<terms.size();i++)
		{
			String t=(String)terms.elementAt(i);
			outputc+="\""+t+"\" => "+i+",\r\n";
		}
		outputc+=");\r\n";

		// build rules array
		outputc+="\r\n";
		outputc+="my @rules=\r\n(\r\n";
		for(i=0;i<rules.size();i++)
		{
			Vector v=(Vector)rules.elementAt(i);
			int inonterm=nonterms.indexOf((String)v.elementAt(0));
			if(inonterm==-1)
				throw new Exception("Error; lhs not in nonterminal vector\r\n");
			outputc+="[ "+inonterm+","+(v.size()-1)+" ],\r\n";
		}
		outputc+=");\r\n";

		// build action table
		outputc+="\r\n";
		outputc+="my @action=\r\n(\r\n";
		for(i=0;i<action.size();i++)
		{
			Hashtable ht=(Hashtable)action.elementAt(i);
			outputc+="[";
			for(j=0;j<terms.size();j++)
			{
				String t=(String)terms.elementAt(j);
				if(ht.containsKey(t))
				{
					String t2=(String)ht.get(t);
					if(t2.startsWith("s"))
					{
						// shift
						outputc+="[ $INST_SHIFT,"+t2.substring(1)+"],";
					}
					else if(t2.startsWith("r"))
					{
						// reduce
						outputc+="[ $INST_REDUCE,"+t2.substring(1)+"],";
					}
					else if(t2.startsWith("a"))
					{
						// accept
						outputc+="[ $INST_ACCEPT,0 ],";
					}
					else
					{
						// error
						outputc+="[ $INST_ERROR,0 ],";
					}
				}
				else
				{
					// error
					outputc+="[ $INST_ERROR,0 ],";
				}
			}
			outputc+=" ],\r\n";
		}
		outputc+=");\r\n";

		// build goto table
		outputc+="\r\n";
		outputc+="my @gototab=\r\n(\r\n";
		for(i=0;i<LR0goto.size();i++)
		{
			Hashtable ht=(Hashtable)LR0goto.elementAt(i);
			outputc+="[";
			for(j=0;j<nonterms.size();j++)
			{
				String t=(String)nonterms.elementAt(j);
				if(ht.containsKey(t))
				{
					outputc+=ht.get(t)+",";
				}
				else
				{
					outputc+="-1,";
				}
			}
			outputc+="],\r\n";
		}
		outputc+=");\r\n";

		// build semantic actions functions
		outputc+="\r\n";
		outputc+="sub semactions\r\n";
		outputc+="{\r\n";
		outputc+="	my $r=shift;\r\n";
		outputc+="	my $rclval;\r\n";
		for(i=0;i<semactions.size();i++)
		{
			String t=(String)semactions.elementAt(i);
			if(i==0)
			{
				outputc+="	if($r=="+i+")\r\n{\r\n"+parseSemaction3(t,i)+"\r\n}\r\n";
			}
			else
			{
				outputc+="	elsif($r=="+i+")\r\n{\r\n"+parseSemaction3(t,i)+"\r\n}\r\n";
			}
		}
		outputc+="}\r\n";

		outputc+="\r\n";
		outputc+="sub "+PREFIX+"error\r\n";
		outputc+="{\r\n";
		outputc+="	my $errmsg=shift;\r\n";
		outputc+="	print $errmsg.\"\\r\\n\";\r\n";
		outputc+="}\r\n";

		outputc+="\r\n";
		outputc+="sub "+PREFIX+"parse\r\n";
		outputc+="{\r\n";
		outputc+="	my $c="+PREFIX+"lex();\r\n";
		outputc+="	my ($ic,$s,$inst,$param,$tmp);\r\n";
		outputc+="	$stack[++$#stack]=0;\r\n";
		outputc+="	$vstack[++$#vstack]=$"+PREFIX+"lval;\r\n";
		outputc+="	MAINLOOP: while(1)\r\n";
		outputc+="	{\r\n";
		outputc+="		$ic=$termmap{$c};\r\n";
		outputc+="		if(not defined $ic)\r\n";
		outputc+="		{\r\n";
		outputc+="			$inst=$INST_ERROR;\r\n";
		outputc+="		}\r\n";
		outputc+="		else\r\n";
		outputc+="		{\r\n";
		outputc+="			$s=$stack[$#stack];\r\n";
		outputc+="			$inst=$action[$s][$ic][0];\r\n";
		outputc+="			$param=$action[$s][$ic][1];\r\n";
		outputc+="		}\r\n";
		outputc+="		if($inst==$INST_SHIFT)\r\n";
		outputc+="		{\r\n";
		outputc+="			$stack[++$#stack]=$ic;\r\n";
		outputc+="			$stack[++$#stack]=$param;\r\n";
		outputc+="			$c="+PREFIX+"lex();\r\n";
		outputc+="			$vstack[++$#vstack]=$"+PREFIX+"lval;\r\n";
		outputc+="		}\r\n";
		outputc+="		elsif($inst==$INST_REDUCE)\r\n";
		outputc+="		{\r\n";
		outputc+="			$#stack-=2*$rules[$param][1];\r\n";
		outputc+="			if($#stack<0)	{	"+PREFIX+"error(\"error, stack underflow\\r\\n\");	last MAINLOOP;	}\r\n";
		outputc+="			$tmp=$gototab[$stack[$#stack]][$rules[$param][0]];\r\n";
		outputc+="			$stack[++$#stack]=$rules[$param][0];\r\n";
		outputc+="			if($tmp<0)	{	"+PREFIX+"error(\"error in gototab\\r\\n\");	last MAINLOOP;	}\r\n";
		outputc+="			$stack[++$#stack]=$tmp;\r\n";
		outputc+="			$"+PREFIX+"lval=$vstack[$#vstack--];\r\n";/*temporarily remove value of recently shifted token*/
		outputc+="			semactions($param);\r\n";
		outputc+="			$vstack[++$#vstack]=$"+PREFIX+"lval;\r\n";
		outputc+="		}\r\n";
		outputc+="		elsif($inst==$INST_ACCEPT)\r\n";
		outputc+="		{\r\n";
		outputc+="			last MAINLOOP;\r\n";
		outputc+="		}\r\n";
		outputc+="		else\r\n";
		outputc+="		{\r\n";
		outputc+="			$tmp=0;\r\n";	// not used?
		outputc+="			$ic=$termmap{\""+ERROR+"\"};\r\n";
		outputc+="			while(1)\r\n";
		outputc+="			{\r\n";
		outputc+="				$#stack-=2;\r\n";
		outputc+="				if($#stack<0)	{	"+PREFIX+"error(\"error!\\r\\n\");	last MAINLOOP; };\r\n";
		outputc+="				$s=$stack[$#stack];\r\n";
		outputc+="				$inst=$action[$s][$ic][0];\r\n";
		outputc+="				$param=$action[$s][$ic][1];\r\n";
		outputc+="				if($inst==$INST_SHIFT)\r\n";
		outputc+="				{\r\n";
		outputc+="					$stack[++$#stack]=$ic;\r\n";
		outputc+="					$stack[++$#stack]=$param;\r\n";
		outputc+="					$c="+PREFIX+"lex();\r\n";
		outputc+="					$vstack[++$#vstack]=$"+PREFIX+"lval;\r\n";
		outputc+="					last;\r\n";
		outputc+="				}\r\n";
		outputc+="			}\r\n";
		outputc+="		}\r\n";
		outputc+="	}\r\n";
		outputc+="}\r\n";

		outputc+="\r\n#supporting code\r\n"+support;
	}

/////////////////////////////////////// Python ///////////////////////////////////////

	// replace the $n's, etc. in { ... }
	String parseSemaction4(String s, int ruleno)	throws Exception
	{
		Vector v=(Vector)rules.elementAt(ruleno);
		int rhslen=v.size()-1;

		String so="";

		if(s.length()<1)
		{
			return "\t\tvstack[len(vstack)-"+(rhslen-1)+":]=[]";
		}

		int pos=1,pos2=1,len=s.length();	// skip '{'
		char c;
		if(rhslen>0)
			so+="\t\trclval=vstack[len(vstack)-"+(rhslen)+"]\r\n";
		else	// if an epsilon production
			so+="\t\trclval=0\r\n";
		while(pos<len-1)
		{
			c=s.charAt(pos);
			if(Character.isWhitespace(c))	// skip whitespace
			{
				pos++;
				continue;
			}
			if(c=='\"')	// skip string literal
			{
				pos++;
				while(s.charAt(pos)!='\"')
				{
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					if(s.charAt(pos)=='\\')	// escape sequence
					{
						pos++;
						if(pos>=len-1)
							throw new Exception("Syntax error in semantic action section\r\n");
					}
					pos++;
				}
				pos++;
				continue;
			}
			if(c=='\'')	// skip character literal
			{
				pos++;
				while(s.charAt(pos)!='\'')
				{
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					if(s.charAt(pos)=='\\')	// escape sequence
					{
						pos++;
						if(pos>=len-1)
							throw new Exception("Syntax error in semantic action section\r\n");
					}
					pos++;
				}
				pos++;
				continue;
			}
			if(c=='/')
			{
				pos++;
				if(pos>=len-1)
					throw new Exception("Syntax error in semantic action section\r\n");
				if(s.charAt(pos)=='*')
				{
					pos++;
					// comment begins
					if((pos=s.indexOf("*/",pos))==-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					pos+=2;
				}
				continue;
			}
			if(c=='$')
			{
				pos++;
				if(pos>=len-1)
					throw new Exception("Syntax error in semantic action section\r\n");
				if(s.charAt(pos)=='$')
				{
					so+=s.substring(pos2,pos-1);
					so+="rclval";
					pos++;
					pos2=pos;
					continue;
				}
				if(Character.isDigit(s.charAt(pos)))
				{
					so+=s.substring(pos2,pos-1);
					pos2=pos++;
					while(Character.isDigit(s.charAt(pos)))
					{
						pos++;
					}
					if(pos>=len-1)
						throw new Exception("Syntax error in semantic action section\r\n");
					int idx=Integer.parseInt(s.substring(pos2,pos));
					if(idx>rhslen || idx<1)
						throw new Exception("Error in semantic action section, index out of range\r\n");
					so+="vstack[len(vstack)-"+(rhslen-idx+1)+"]";
					pos2=pos;
					continue;
				}
				pos++;
				continue;
			}
			pos++;
		}
		so+="\t\t"+s.substring(pos2,pos);
		so+="\r\n\t\tvstack[len(vstack)-"+(rhslen)+":]=[]\r\n";
		so+="\t\tvstack.append(rclval)";
		return so;
	}

	// write Python code implementation
	void genPythonCode() throws Exception
	{
		int i,j;

		outputc+="#"+APPNAME+" generated source file, by Rhonald C. Lua.  (C) 2000 All rights reserved.\r\n";
		outputc+="#Notes:\r\n#You must provide an implementation of the lexer \'"+PREFIX+"lex()\'\r\n";
		outputc+="#which returns a token code in the format \'<char>\' for character literals and the symbol name for other terminals\r\n";
		outputc+="\r\n#start of literal block\r\n";
		outputc+=lit;
		outputc+="#end of literal block\r\n\r\n";
		outputc+="NUMTERMS="+terms.size()+"\r\n";
		outputc+="NUMNONTERMS="+nonterms.size()+"\r\n";
		outputc+="NUMRULES="+rules.size()+"\r\n";
		outputc+="NUMSTATES="+LR0.size()+"\r\n";
		outputc+="INST_ERROR=-1\r\n";
		outputc+="INST_SHIFT=0\r\n";
		outputc+="INST_REDUCE=1\r\n";
		outputc+="INST_ACCEPT=2\r\n";

		outputc+="\r\n";
		outputc+="jjlval=0\r\n";
		outputc+="stack=[]\r\n";
		outputc+="vstack=[]\r\n";

		// build terminal map
		outputc+="\r\n";
		outputc+="termmap={\r\n";
		for(i=0;i<terms.size();i++)
		{
			String t=(String)terms.elementAt(i);
			outputc+="\""+t+"\" : "+i+",\r\n";
		}
		outputc+="}\r\n";

		// build rules array
		outputc+="\r\n";
		outputc+="rules=[\r\n";
		for(i=0;i<rules.size();i++)
		{
			Vector v=(Vector)rules.elementAt(i);
			int inonterm=nonterms.indexOf((String)v.elementAt(0));
			if(inonterm==-1)
				throw new Exception("Error; lhs not in nonterminal vector\r\n");
			outputc+="[ "+inonterm+","+(v.size()-1)+" ],\r\n";
		}
		outputc+="]\r\n";

		// build action table
		outputc+="\r\n";
		outputc+="action=[\r\n";
		for(i=0;i<action.size();i++)
		{
			Hashtable ht=(Hashtable)action.elementAt(i);
			outputc+="[";
			for(j=0;j<terms.size();j++)
			{
				String t=(String)terms.elementAt(j);
				if(ht.containsKey(t))
				{
					String t2=(String)ht.get(t);
					if(t2.startsWith("s"))
					{
						// shift
						outputc+="[ INST_SHIFT,"+t2.substring(1)+"],";
					}
					else if(t2.startsWith("r"))
					{
						// reduce
						outputc+="[ INST_REDUCE,"+t2.substring(1)+"],";
					}
					else if(t2.startsWith("a"))
					{
						// accept
						outputc+="[ INST_ACCEPT,0 ],";
					}
					else
					{
						// error
						outputc+="[ INST_ERROR,0 ],";
					}
				}
				else
				{
					// error
					outputc+="[ INST_ERROR,0 ],";
				}
			}
			outputc+=" ],\r\n";
		}
		outputc+="]\r\n";

		// build goto table
		outputc+="\r\n";
		outputc+="gototab=[\r\n";
		for(i=0;i<LR0goto.size();i++)
		{
			Hashtable ht=(Hashtable)LR0goto.elementAt(i);
			outputc+="[";
			for(j=0;j<nonterms.size();j++)
			{
				String t=(String)nonterms.elementAt(j);
				if(ht.containsKey(t))
				{
					outputc+=ht.get(t)+",";
				}
				else
				{
					outputc+="-1,";
				}
			}
			outputc+="],\r\n";
		}
		outputc+="]\r\n";

		// build semantic actions functions
		outputc+="\r\n";
		outputc+="def semactions(r):\r\n";
		outputc+="	global stack,vstack\r\n";
		for(i=0;i<semactions.size();i++)
		{
			String t=(String)semactions.elementAt(i);
			if(i==0)
			{
				outputc+="	if r=="+i+":\r\n"+parseSemaction4(t,i)+"\r\n";
			}
			else
			{
				outputc+="	elif r=="+i+":\r\n"+parseSemaction4(t,i)+"\r\n";
			}
		}

		outputc+="\r\n";
		outputc+="def "+PREFIX+"error(msg):\r\n";
		outputc+="	print msg\r\n";

		outputc+="\r\n";
		outputc+="def "+PREFIX+"parse():\r\n";
		outputc+="	global jjlval,stack,vstack,bufptr\r\n";
		outputc+="	c="+PREFIX+"lex()\r\n";
		outputc+="	stack.append(0)\r\n";
		outputc+="	vstack.append("+PREFIX+"lval)\r\n";
		outputc+="	while 1:\r\n";
		outputc+="		try:\r\n";
		outputc+="			ic=termmap[c]\r\n";
		outputc+="			s=stack[-1];\r\n";
		outputc+="			inst=action[s][ic][0]\r\n";
		outputc+="			param=action[s][ic][1]\r\n";
		outputc+="		except:	inst=INST_ERROR\r\n";
		outputc+="		if inst==INST_SHIFT:\r\n";
		outputc+="			stack.append(ic)\r\n";
		outputc+="			stack.append(param)\r\n";
		outputc+="			c="+PREFIX+"lex()\r\n";
		outputc+="			vstack.append("+PREFIX+"lval)\r\n";
		outputc+="		elif inst==INST_REDUCE:\r\n";
		outputc+="			try:\r\n";
		outputc+="				stack[len(stack)-2*rules[param][1]:]=[]\r\n";
		outputc+="			except:\r\n";
		outputc+="				"+PREFIX+"error(\"error, stack underflow\\r\\n\")\r\n";
		outputc+="				break\r\n";
		outputc+="			tmp=gototab[stack[-1]][rules[param][0]]\r\n";
		outputc+="			stack.append(rules[param][0])\r\n";
		outputc+="			if tmp<0:\r\n";
		outputc+="				"+PREFIX+"error(\"error in gototab\\r\\n\")\r\n";
		outputc+="				break\r\n";
		outputc+="			stack.append(tmp)\r\n";
		outputc+="			"+PREFIX+"lval=vstack.pop()\r\n";/*temporarily remove value of recently shifted token*/
		outputc+="			semactions(param)\r\n";
		outputc+="			vstack.append("+PREFIX+"lval)\r\n";
		outputc+="		elif inst==INST_ACCEPT:\r\n";
		outputc+="			break\r\n";
		outputc+="		else:\r\n";
		outputc+="			tmp=0\r\n";
		outputc+="			ic=termmap[\""+ERROR+"\"]\r\n";
		outputc+="			while 1:\r\n";
		outputc+="				try:\r\n";
		outputc+="					stack.pop()\r\n";
		outputc+="					stack.pop()\r\n";
		outputc+="				except:\r\n";
		outputc+="					"+PREFIX+"error(\"error!\\r\\n\")\r\n";
		outputc+="					tmp=1\r\n";
		outputc+="					break\r\n";
		outputc+="				s=stack[-1]\r\n";
		outputc+="				inst=action[s][ic][0]\r\n";
		outputc+="				param=action[s][ic][1]\r\n";
		outputc+="				if inst==INST_SHIFT:\r\n";
		outputc+="					stack.append(ic)\r\n";
		outputc+="					stack.append(param)\r\n";
		outputc+="					c="+PREFIX+"lex()\r\n";
		outputc+="					vstack.append("+PREFIX+"lval)\r\n";
		outputc+="					break\r\n";
		outputc+="			if tmp==1: break\r\n";

		outputc+="\r\n#supporting code\r\n"+support;
	}

	void genCode() throws Exception
	{
		if((option & 0x01)>0)
		{
			genANSICCode();
			genTrace();
			outputc+="\r\n/**********begin trace**********\r\n\r\n"+trace+"\r\n**********end trace**********/\r\n";
		}
		else if((option & 0x02)>0)
		{
			genJavaCode();
			genTrace();
			outputc+="\r\n/**********begin trace**********\r\n\r\n"+trace+"\r\n**********end trace**********/\r\n";
		}
		else if((option & 0x04)>0)
		{
			genPERLCode();
			genTrace();
		}
		else if((option & 0x08)>0)
		{
			genPythonCode();
			genTrace();
		}
	}
}
// end Jacc