/*------------------------------------------------------------------------------------
this file is part of notepad++
Copyright (C)2003 Don HO < donho@altern.org >

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
----------------------------------------------------------------------------------------*/
#include <stdlib.h>
#include <string>
#include <map>
#include <vector>
#include <ctype.h>
#include <stdio.h>
#include <stdarg.h>
#include <assert.h>
#include <windows.h>

#include "Platform.h"

#include "ILexer.h"
#include "LexAccessor.h"
#include "Accessor.h"
#include "StyleContext.h"
#include "WordList.h"
#include "Scintilla.h"
#include "SciLexer.h"
#include "CharClassify.h"
#include "LexerModule.h"
#include "PropSetSimple.h"
#include "SplitVector.h"
#include "Partitioning.h"
#include "RunStyles.h"
#include "CellBuffer.h"
#include "PerLine.h"
#include "Decoration.h"
#include "Document.h"

#ifdef SCI_NAMESPACE
using namespace Scintilla;
#endif

const int maskMapperKeywords[] = {
	SCE_USER_MASK_NESTING_KEYWORD1,
	SCE_USER_MASK_NESTING_KEYWORD2,
	SCE_USER_MASK_NESTING_KEYWORD3,
	SCE_USER_MASK_NESTING_KEYWORD4,
	SCE_USER_MASK_NESTING_KEYWORD5,
	SCE_USER_MASK_NESTING_KEYWORD6,
	SCE_USER_MASK_NESTING_KEYWORD7,
	SCE_USER_MASK_NESTING_KEYWORD8
};

#define COMMENTLINE_NO    			0
#define COMMENTLINE_YES    			1
#define COMMENTLINE_SKIP_TESTING    2

#define FOLD_NONE   0
#define FOLD_OPEN   1
#define FOLD_MIDDLE 2
#define FOLD_CLOSE  3

#define NI_OPEN	    0
#define NI_CLOSE    1

#define NUMBER_NOT_A_NUMBER   0
#define NUMBER_DECIMAL	      1
#define NUMBER_EXTRA_CHAR     2
#define NUMBER_RANGE_CHAR     3

using namespace std;
static vector<nestedInfo> nestedVector;
static vector<foldInfo> foldVector;

struct forwardStruct {
	vvstring * vec;
	int sceID;
	int maskID;

	forwardStruct():vec(0), sceID(0), maskID(0) {};	// constructor, useless but obligatory

	forwardStruct * Set (vvstring * vec, int sceID, int maskID) {
		this->vec = vec;
		this->sceID = sceID;
		this->maskID = maskID;
		return this;
	}

}FWS;	// just one instance

static nestedInfo NI;   // also just one instance

static inline bool IsADigit(char ch) {
    return isascii(ch) && isdigit(ch);
}

static inline int isADigit(StyleContext & sc, bool ignoreCase, vector<string> & extraCharTokens,
					bool hasPrefix, vector<string> & extrasInPrefixedTokens)
{
	if (IsADigit(sc.ch))
		return NUMBER_DECIMAL;

	vector<string>::iterator iter;
	if (hasPrefix)
	{
		iter = extrasInPrefixedTokens.begin();
		for (; iter != extrasInPrefixedTokens.end(); ++iter)
		if (ignoreCase ? sc.MatchIgnoreCase(iter->c_str()) : sc.Match(iter->c_str()))
			return NUMBER_EXTRA_CHAR;
	}

	iter = extraCharTokens.begin();
	for (; iter != extraCharTokens.end(); ++iter)
		if (ignoreCase ? sc.MatchIgnoreCase(iter->c_str()) : sc.Match(iter->c_str()))
			return NUMBER_RANGE_CHAR;

	return NUMBER_NOT_A_NUMBER;
}

static inline bool isspacechar(unsigned char ch) {
    return (ch == ' ') || ((ch >= 0x09) && (ch <= 0x0d));
}

static inline bool isWhiteSpace(const int ch) {
    return (ch > 0 && ch <0x21);
}

static inline bool isSpaceOrTab(const int ch) {
    return (ch == ' ') || (ch == '\t');
}

static inline void SubGroup(const char * s, vvstring & vec, bool group=false)
{
	unsigned int length = strlen(s);
	char * temp = new char[length+1];
	unsigned int index = 0;
	vector<string> subvector;
	unsigned int i = 0;

	for (unsigned int j=0; j<length+1; ++j)
		temp[j] = 0;

	if (s[0] == '(' && s[1]  == '(')
	{
		i = 2;
		group = true;
	}

	if (s[length-1] == ')' && s[length-2] == ')')
		length -= 2;

	if (!group && *s)
    {
        subvector.push_back(s);
    }
    else
    {
		for (; i<length; ++i)
		{
			if (s[i] == ' ')
			{
				if (*temp)
				{
					if (!strcmp(temp, "EOL"))
					{
						subvector.push_back("\r\n");
						subvector.push_back("\n");
						subvector.push_back("\r");
					}
					else
						subvector.push_back(temp);

					index = 0;
					for (unsigned int j=0; j<length; ++j)
						temp[j] = 0;
				}
			}
			else if (i == length-1)
			{
				temp[index++] = s[i];
				if (*temp)
                {
					if (!strcmp(temp, "EOL"))
					{
						subvector.push_back("\r\n");
						subvector.push_back("\n");
						subvector.push_back("\r");
					}
					else
						subvector.push_back(temp);
                }
			}
			else
			{
				temp[index++] = s[i];
			}
		}
	}

    if (!subvector.empty())
        vec.push_back(subvector);

	delete [] temp;
}

static inline void GenerateVector(vvstring & vec, const char * s, char * prefix, int minLength)
{
	unsigned int length = strlen(s);
	char * temp = new char[length];
	unsigned int index = 0;
	bool copy = false;
	bool inGroup = false;

	for (unsigned int j=0; j<length; ++j)
		temp[j] = 0;

	vec.clear();
	for (unsigned int i=0; i<length; ++i)
	{
        if (copy && !inGroup && s[i] == ' ')
        {
            SubGroup(temp, vec, inGroup);
			index = 0;
			copy = false;
			for (unsigned int j=0; j<length; ++j)
				temp[j] = 0;
        }

        if ( (s[i] == ' ' && s[i+1] == prefix[0] && s[i+2] == prefix[1] && s[i+3] != ' ') ||
			 (   i == 0   &&   s[0] == prefix[0] &&   s[1] == prefix[1] && s[i+2] != ' ') )
        {
			if (i > 0)	i += 1;	// skip space
			i += 2;				// skip prefix
			copy = true;

			if (s[i] == ' ')
				continue;

			if (s[i] == '(' && s[i+1] == '(')
				inGroup = true;
        }

		if (inGroup && s[i] == ')' && s[i+1] == ')')
			inGroup = false;

		if (copy)
			temp[index++] = s[i];
    }

	if (length)
		SubGroup(temp, vec, inGroup);

    vector<string> emptyVector;
    for (int i = vec.size(); i < minLength; ++i)
    {
        vec.push_back(emptyVector);
    }

	delete [] temp;
}

static bool CheckLineContinuation(vvstring & commentLineContinue, Accessor & styler, int openIndex, int startPos, bool ignoreCase)
{
	int offset = 0;
	vvstring::iterator iter = commentLineContinue.begin();
	if (openIndex != -1)
		iter += openIndex;

	bool lineContinuation = false;

	for (; iter != commentLineContinue.end(); ++iter)
	{
		offset = 0;
		if (styler.SafeGetCharAt(startPos - 1) == '\r')
			offset = 1;

		vector<string>::iterator iter2 = iter->begin();
		for (; iter2 != iter->end(); ++iter2)
		{
			int length = iter2->length();
			if (length == 0)
				continue;

			lineContinuation = true;
			for (int i=0; i<length; ++i)
			{
				if (ignoreCase)
				{
					if (toupper((*iter2)[i]) != toupper(styler.SafeGetCharAt(startPos - length + i - offset, 0)))
					{
						lineContinuation = false;
						break;
					}
				}
				else if ((*iter2)[i] != styler.SafeGetCharAt(startPos - length + i - offset, 0))
				{
					lineContinuation = false;
					break;
				}
			}
			if (lineContinuation)
				break;
		}
		if (lineContinuation || openIndex != -1)
			break;
	}

	return lineContinuation;
}


static inline void ReColoringCheck ( unsigned int & startPos, int & initStyle, unsigned int & nestedLevel, int & openIndex,
                                     int & isPrevLineComment,  bool & isInCommentBlock, unsigned int & commentBlockStart,
								     bool & setFoldEndAtEOL,  Accessor & styler, bool & isInComment, int & isCommentLine,
								     vector<nestedInfo> & lastNestedGroup )
{
	// Re-coloring always starts at line begining.
	// To check comment blocks we need to unconditionally go back to start of previous line.

	// skip EOL chars
	if (styler.SafeGetCharAt(--startPos) == '\n')
	{
		if (styler.SafeGetCharAt(--startPos) == '\r')
			--startPos;
	}
	if (static_cast<int>(startPos) < 0)
		startPos = 0;

	// go back until first EOL char
	char ch = 0;
	do
	{
		ch = styler.SafeGetCharAt(startPos--);
		if (startPos == -1)
			startPos = 0;
	}
	while(ch != '\r' && ch != '\n' && startPos > 0);
	if (startPos > 0)
		startPos += 2;  // compensate for decrement operations

	if (startPos == 0)
	{
		foldVector.clear();
        nestedVector.clear();
		lastNestedGroup.clear();
		initStyle = SCE_USER_STYLE_DEFAULT;
		return;
	}

	// special exception for multipart keywords
	initStyle = styler.StyleAt(startPos-1); // check style of previous new line character 
    if ( (initStyle >= SCE_USER_STYLE_KEYWORD1 && initStyle < (SCE_USER_STYLE_KEYWORD1+SCE_USER_TOTAL_KEYWORDS)) 
        || initStyle == SCE_USER_STYLE_FOLDER_IN_COMMENT )
    {
        // we are in multi-part keyword, go back until current style ends
        while (startPos >= 0 && styler.StyleAt(--startPos) == initStyle);
    }

	// Clear all data on positions forward of 'startPos' as we
	// are about to re-color that part of the document.
    vector<nestedInfo>::iterator iter = nestedVector.begin();
	for (; iter != nestedVector.end(); ++iter)
	{
		if (iter->position >= startPos)
		{
			nestedVector.erase(iter, nestedVector.end());
			break;
		}
	}

    if (!nestedVector.empty())
    {
		// go back to last level '1' (or begining of vector)
        iter = --nestedVector.end();
		lastNestedGroup.clear();
		while (iter->nestedLevel > 1 && iter != nestedVector.begin())
			--iter;
    }
	else
    {
		iter = nestedVector.end();
    }

	// recreate lastNestedGroup, skip adjecent OPEN/CLOSE pairs
	vector<nestedInfo>::iterator last;
	while (iter != nestedVector.end())
	{
		if (iter->opener == NI_OPEN)
			lastNestedGroup.push_back(*iter);
		else if (iter->opener == NI_CLOSE && !lastNestedGroup.empty())
		{
			last = --lastNestedGroup.end();
			if (last->opener == NI_OPEN)
			{
				if (last->nestedLevel == iter->nestedLevel && last->state == iter->state && last->index == iter->index)
				{
					lastNestedGroup.erase(last);
				}
			}
		}
		++iter;
	}

	if (!lastNestedGroup.empty())
	{
		last = --lastNestedGroup.end();
		initStyle = last->state;
		openIndex = last->index;
		nestedLevel = last->nestedLevel;

		// are we nested somewhere in comment?
		for (; ; --last)
		{
			if (last->state == SCE_USER_STYLE_COMMENT)
			{
				isInComment = true;
				isCommentLine = COMMENTLINE_YES;
			}
			if (last->state == SCE_USER_STYLE_COMMENTLINE)
			{
				isCommentLine = COMMENTLINE_YES;
			}
			if (last == lastNestedGroup.begin())
				break;
		}
	}
	else
	{
		initStyle = SCE_USER_STYLE_DEFAULT;
		openIndex = -1;
		nestedLevel = 0;
	}

	// Clear all data on positions forward of 'startPos' as we
	// are about to re-color that part of the document.
	vector<foldInfo>::iterator fiter = foldVector.begin();
	for (; fiter != foldVector.end(); ++fiter)
	{
		if (fiter->position >= startPos)
		{
			foldVector.erase(fiter, foldVector.end());
			break;
		}
	}

	// are we in fold block of commented lines?
	if (!foldVector.empty())
	{
		fiter = foldVector.end() - 1;
		if ((fiter->state == FOLD_OPEN || fiter->state == FOLD_MIDDLE) && fiter->isFoldStatement == false)
		{
			isPrevLineComment = COMMENTLINE_YES;
			isInCommentBlock  = true;
			commentBlockStart = 1; // any value != -1 will do
		}
	}

	if (isInCommentBlock && startPos > 0)
	{
		// set end of previous line as possible comment line block end position
		setFoldEndAtEOL = true;
	}
}

static inline void CommentBlockCheck(int & isPrevLineComment, int & isCommentLine,	bool & isInCommentBlock, unsigned int & commentBlockStart,
								     unsigned int & commentBlockEnd, StyleContext & sc, bool & isInComment,  bool & setFoldEndAtEOL, int & foldInComment)
{
	if (foldInComment != FOLD_NONE)
		isCommentLine = COMMENTLINE_SKIP_TESTING;

	if (setFoldEndAtEOL && isCommentLine != COMMENTLINE_SKIP_TESTING)
	{
		commentBlockEnd = sc.currentPos;
		setFoldEndAtEOL = false;
	}

	if ((isInCommentBlock && isCommentLine != COMMENTLINE_YES && isPrevLineComment == COMMENTLINE_YES))
	{
		if (commentBlockEnd > 0)
		{
			foldInfo fi = {commentBlockEnd, FOLD_CLOSE, false};
			foldVector.push_back(fi);
		}
		isInCommentBlock = false;
	}

	if (!isInCommentBlock)
		if (isCommentLine == COMMENTLINE_YES)
			if (isPrevLineComment == COMMENTLINE_YES)
				if (commentBlockStart != -1)
	{
		foldInfo fi = {commentBlockStart, FOLD_OPEN, false};
		foldVector.push_back(fi);

		commentBlockStart = static_cast<unsigned int>(-1);
		isInCommentBlock = true;
	}

	if (isCommentLine != COMMENTLINE_YES)
	{
		commentBlockStart = static_cast<unsigned int>(-1);
		commentBlockEnd = 0;
	}

	isPrevLineComment = isCommentLine==COMMENTLINE_YES ? COMMENTLINE_YES:COMMENTLINE_NO;
	if (isInComment)
		isCommentLine = COMMENTLINE_YES;
	else
		isCommentLine = COMMENTLINE_NO;

	if (foldInComment != FOLD_NONE)
	{
		foldInfo fi = {sc.currentPos, foldInComment, true};
		foldVector.push_back(fi);
		foldInComment = FOLD_NONE;
		isPrevLineComment = COMMENTLINE_NO;
	}
}

static bool isInList2(vvstring & openVector, StyleContext & sc, bool ignoreCase, int & openIndex, int & skipForward)
{
    skipForward = 0;
	vector<vector<string>>::iterator iter1 = openVector.begin();
	vector<string>::iterator iter2;

	for (; iter1 != openVector.end(); ++iter1)
	{
		iter2 = iter1->begin();
		for (; iter2 != iter1->end(); ++iter2)
		{
			if (ignoreCase?sc.MatchIgnoreCase(iter2->c_str()):sc.Match(iter2->c_str()))
			{
                openIndex = iter1 - openVector.begin();
                skipForward = iter2->length();
				return true;
			}
		}
	}

	return false;
}

static bool isInList3(vvstring & openVector, StyleContext & sc, bool ignoreCase, int forward)
{
	vvstring::iterator iter1 = openVector.begin();
	vector<string>::iterator iter2;
	string::iterator iter3;
    int index = 0;
	int a = 0;
	int b = 0;

	for (; iter1 != openVector.end(); ++iter1)
	{
		iter2 = iter1->begin();
		for (; iter2 != iter1->end(); ++iter2)
		{
            iter3 = iter2->begin();
            index = 0;
            for (; iter3 != iter2->end(); ++iter3)
            {
                a = ignoreCase?toupper(*iter3):*iter3;
                b = ignoreCase?toupper(sc.GetRelative(forward + index++)):sc.GetRelative(forward + index++);
                if (a != b)
                    return false;
            }
		}
	}

	return false;
}

static bool isInList(WordList & list, StyleContext & sc, bool specialMode, bool ignoreCase, int & moveForward, vvstring * multiPartEndVectors[])
{
	if (!list.words)
        return false;

	moveForward = 0;
	int offset = -1 * sc.LengthCurrent();
	unsigned char firstChar = sc.GetRelative(offset);
    int i = list.starts[firstChar];
	int a = 0;
	int b = 0;
	int indexa = 0;
	int indexb = 0;
	bool hasVTab = false;
	bool hasBSpace = false;

    if (i >= 0)
    {
		while ((ignoreCase?toupper(list.words[i][0]):list.words[i][0]) == (ignoreCase?toupper(firstChar):firstChar))
		{
			a = 0;
			b = 0;
			indexa = 0;
			indexb = 0;
			hasVTab = false;
			hasBSpace = false;

			do
			{
				a = ignoreCase?toupper(list.words[i][indexa++]):list.words[i][indexa++];
				if (a == '\v')
				{
					hasVTab = true;
					b = sc.GetRelative(offset + indexb++);
					if (isWhiteSpace(b))
					{
						do {b = sc.GetRelative(offset + indexb++);}
						while(isWhiteSpace(b));

						a = ignoreCase?toupper(list.words[i][indexa++]):list.words[i][indexa++];
					}
				}
                else if (a == '\b')
                {
					hasBSpace = true;
					b = sc.GetRelative(offset + indexb++);
					if (isSpaceOrTab(b))
					{
						do {b = sc.GetRelative(offset + indexb++);}
						while(isSpaceOrTab(b));

						a = ignoreCase?toupper(list.words[i][indexa++]):list.words[i][indexa++];
					}
                }
				else
					b = ignoreCase?toupper(sc.GetRelative(offset + indexb++)):sc.GetRelative(offset + indexb++);
			}
			while (a && (a == b));

            if (!a && specialMode && (hasVTab || hasBSpace))
            {
                if (hasVTab && isWhiteSpace(b))
                {
                    // first, skip whitespace (and there must be a white space !!)
                    while(isWhiteSpace(sc.GetRelative(offset + indexb++)));

                    // second, skip next "word"
					bool breakOut = false;
                    while (!isWhiteSpace(sc.GetRelative(indexb + offset)))
                    {
                        for (int i=0; i<SCE_USER_TOTAL_DELIMITERS+6; ++i)
                        {
                            if (!multiPartEndVectors[i]->empty() && isInList3(*multiPartEndVectors[i], sc, ignoreCase, indexb + offset))
							{
								breakOut = true;
								break;
							}
                        }
						if (breakOut)
							break;
                        ++indexb;
                    }
                    ++indexb;
                }
                else if (hasBSpace && isSpaceOrTab(b))
                {
                    // first, skip whitespace (and there must be a white space !!)
                    while(isSpaceOrTab(sc.GetRelative(offset + indexb++)));

                    // second, skip next "word"
					bool breakOut = false;
                    while (!isSpaceOrTab(sc.GetRelative(indexb + offset)))
                    {
                        for (int i=0; i<SCE_USER_TOTAL_DELIMITERS+6; ++i)
                        {
                            if (!multiPartEndVectors[i]->empty() && isInList3(*multiPartEndVectors[i], sc, ignoreCase, indexb + offset))
							{
								breakOut = true;
								break;
							}
                        }
						if (breakOut)
							break;
						++indexb;
                    }
					++indexb;
                }
            }

			if (!a)
			{
                moveForward = indexb + offset - 1;	// offset is already negative
				if (moveForward >= 0)
					return true;
                else if (specialMode)
					return true;
			}
			++i;
		}
	}

	return false;
}

static void setBackwards(WordList * keywordlists[], StyleContext & sc, bool prefixes[], bool ignoreCase,
						 int & foldInComment, int nestedKey, vvstring * multiPartEndVectors[])
{
	if (sc.LengthCurrent() == 0)
		return;

	int moveForward = 0;

	for (int i=0; i<SCE_USER_TOTAL_KEYWORDS; ++i)
	{
		if (nestedKey & maskMapperKeywords[i])
		{
			if (isInList(*keywordlists[i+SCE_USER_KWLIST_KEYWORDS1], sc, prefixes[i], ignoreCase, moveForward, multiPartEndVectors))
			{
				if (moveForward > 0)
					sc.Forward(moveForward);
				sc.ChangeState(i+SCE_USER_STYLE_KEYWORD1);
				return;
			}
		}
	}

	int verdict = FOLD_NONE;
    //TODO: what if nesting happens on the same line, e.g. {aa{bb}cc}if{aa{bb{cc}dd} 

	if (nestedKey & SCE_USER_MASK_NESTING_FOLDERS_IN_CODE2_OPEN)
    {
		if (isInList(*keywordlists[SCE_USER_KWLIST_FOLDERS_IN_CODE2_OPEN], sc, false, ignoreCase, moveForward, multiPartEndVectors))
        {
			if (moveForward > 0)
				sc.Forward(moveForward);
			verdict = FOLD_OPEN;
			sc.ChangeState(SCE_USER_STYLE_FOLDER_IN_CODE2);
		}
	}
	if (nestedKey & SCE_USER_MASK_NESTING_FOLDERS_IN_CODE2_MIDDLE)
    {
		if (isInList(*keywordlists[SCE_USER_KWLIST_FOLDERS_IN_CODE2_MIDDLE], sc, false, ignoreCase, moveForward, multiPartEndVectors))
        {
			if (moveForward > 0)
				sc.Forward(moveForward);
			verdict = FOLD_MIDDLE;
			sc.ChangeState(SCE_USER_STYLE_FOLDER_IN_CODE2);
		}
	}
	if (nestedKey & SCE_USER_MASK_NESTING_FOLDERS_IN_CODE2_CLOSE)
    {
		if (isInList(*keywordlists[SCE_USER_KWLIST_FOLDERS_IN_CODE2_CLOSE], sc, false, ignoreCase, moveForward, multiPartEndVectors))
        {
			if (moveForward > 0)
				sc.Forward(moveForward);
			verdict = FOLD_CLOSE;
			sc.ChangeState(SCE_USER_STYLE_FOLDER_IN_CODE2);
		}
	}

	if (nestedKey & SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_OPEN)
    {
		if (isInList(*keywordlists[SCE_USER_KWLIST_FOLDERS_IN_COMMENT_OPEN], sc, false, ignoreCase, moveForward, multiPartEndVectors))
        {
			if (moveForward > 0)
				sc.Forward(moveForward);
			verdict = FOLD_OPEN;
			sc.ChangeState(SCE_USER_STYLE_FOLDER_IN_COMMENT);
        }
	}
	if (nestedKey & SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_MIDDLE)
	{
        if (isInList(*keywordlists[SCE_USER_KWLIST_FOLDERS_IN_COMMENT_MIDDLE], sc, false, ignoreCase, moveForward, multiPartEndVectors))
        {
			if (moveForward > 0)
				sc.Forward(moveForward);
			verdict = FOLD_MIDDLE;
			sc.ChangeState(SCE_USER_STYLE_FOLDER_IN_COMMENT);
        }
	}
	if (nestedKey & SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_CLOSE)
	{
        if (isInList(*keywordlists[SCE_USER_KWLIST_FOLDERS_IN_COMMENT_CLOSE], sc, false, ignoreCase, moveForward, multiPartEndVectors))
        {
			if (moveForward > 0)
				sc.Forward(moveForward);
			verdict = FOLD_CLOSE;
			sc.ChangeState(SCE_USER_STYLE_FOLDER_IN_COMMENT);
        }
    }

	if (verdict == FOLD_OPEN)
	{
		if (foldInComment == FOLD_CLOSE)
            foldInComment = FOLD_MIDDLE;
        else if (foldInComment == FOLD_NONE)
            foldInComment = FOLD_OPEN;
        else
            foldInComment = FOLD_NONE;

		return;
	}
	if (verdict == FOLD_MIDDLE)
	{
        if (foldInComment == FOLD_NONE)
            foldInComment = FOLD_MIDDLE;
        else
            foldInComment = FOLD_NONE;

		return;
	}
	if (verdict == FOLD_CLOSE)
	{
        if (foldInComment == FOLD_NONE || foldInComment == FOLD_MIDDLE)
            foldInComment = FOLD_CLOSE;
        else
            foldInComment = FOLD_NONE;

		return;
	}

	if (nestedKey & SCE_USER_MASK_NESTING_OPERATORS2)
	{
        if (isInList(*keywordlists[SCE_USER_KWLIST_OPERATORS2], sc, false, ignoreCase, moveForward, multiPartEndVectors))
        {
            sc.ChangeState(SCE_USER_STYLE_OPERATOR);
            return;
        }
    }
}

static bool isInListNested(int nestedKey, vector<forwardStruct> & forwards, StyleContext & sc,
							bool ignoreCase, int & openIndex, int & skipForward, int & newState )
{
	int backup = openIndex;
	vector<forwardStruct>::iterator iter = forwards.begin();

	for (; iter != forwards.end(); ++iter)
	{
		if (nestedKey & iter->maskID)
		{
			if (isInList2(*(iter->vec), sc, ignoreCase, openIndex, skipForward))
			{
				newState = iter->sceID;
				return true;
			}
		}
	}

	openIndex = backup;
	return false;
}

static void readLastNested(vector<nestedInfo> & lastNestedGroup, int & newState, int & openIndex)
{
    newState = SCE_USER_STYLE_DEFAULT;
    openIndex = -1;
    if (!lastNestedGroup.empty())
    {
        lastNestedGroup.erase(lastNestedGroup.end()-1);
        if (!lastNestedGroup.empty())
        {
            newState = (--lastNestedGroup.end())->state;
            openIndex = (--lastNestedGroup.end())->index;
        }
    }
}

static inline void stringToVector(char * original, vector<string> & tokenVector, bool negative=false)
{
	string temp = "";
	char * pch = original;
	while (*pch != NULL)
	{
		if (*pch != ' ')
			temp += *pch;
		else if (temp.size() > 0)
		{
			if (negative)
				tokenVector.push_back("-" + temp);
			else
				tokenVector.push_back(temp);

			temp = "";
		}
		++pch;
	}

	if (temp.size() > 0)
	{
		if (negative)
			tokenVector.push_back("-" + temp);
		else
			tokenVector.push_back(temp);
	}
}

static void ColouriseUserDoc(unsigned int startPos, int length, int initStyle, WordList *keywordlists[], Accessor &styler)
{
    bool foldComments   = styler.GetPropertyInt("userDefine.allowFoldOfComments",   0) != 0;
    bool ignoreCase     = styler.GetPropertyInt("userDefine.isCaseIgnored",			0) != 0;

    bool prefixes[8];
    prefixes[0] = styler.GetPropertyInt("userDefine.prefixKeywords1", 0) != 0;
    prefixes[1] = styler.GetPropertyInt("userDefine.prefixKeywords2", 0) != 0;
    prefixes[2] = styler.GetPropertyInt("userDefine.prefixKeywords3", 0) != 0;
    prefixes[3] = styler.GetPropertyInt("userDefine.prefixKeywords4", 0) != 0;
    prefixes[4] = styler.GetPropertyInt("userDefine.prefixKeywords5", 0) != 0;
    prefixes[5] = styler.GetPropertyInt("userDefine.prefixKeywords6", 0) != 0;
    prefixes[6] = styler.GetPropertyInt("userDefine.prefixKeywords7", 0) != 0;
    prefixes[7] = styler.GetPropertyInt("userDefine.prefixKeywords8", 0) != 0;

	char nestingBuffer[] = "userDefine.nesting.00";		// 00 is only a placeholder, the actual number is set by _itoa
	_itoa(SCE_USER_STYLE_COMMENT,  		(nestingBuffer+20), 10);	int commentNesting		= styler.GetPropertyInt(nestingBuffer, 0);
	_itoa(SCE_USER_STYLE_COMMENTLINE,	(nestingBuffer+20), 10);	int lineCommentNesting	= styler.GetPropertyInt(nestingBuffer, 0);
	_itoa(SCE_USER_STYLE_DELIMITER1,	(nestingBuffer+19), 10);	int delim1Nesting		= styler.GetPropertyInt(nestingBuffer, 0);	// one byte difference
	_itoa(SCE_USER_STYLE_DELIMITER2,	(nestingBuffer+19), 10);	int delim2Nesting		= styler.GetPropertyInt(nestingBuffer, 0);	// for two-digit numbers
	_itoa(SCE_USER_STYLE_DELIMITER3,	(nestingBuffer+19), 10);	int delim3Nesting		= styler.GetPropertyInt(nestingBuffer, 0);
	_itoa(SCE_USER_STYLE_DELIMITER4,	(nestingBuffer+19), 10);	int delim4Nesting		= styler.GetPropertyInt(nestingBuffer, 0);
	_itoa(SCE_USER_STYLE_DELIMITER5,	(nestingBuffer+19), 10);	int delim5Nesting		= styler.GetPropertyInt(nestingBuffer, 0);
	_itoa(SCE_USER_STYLE_DELIMITER6,	(nestingBuffer+19), 10);	int delim6Nesting		= styler.GetPropertyInt(nestingBuffer, 0);
	_itoa(SCE_USER_STYLE_DELIMITER7,	(nestingBuffer+19), 10);	int delim7Nesting		= styler.GetPropertyInt(nestingBuffer, 0);
	_itoa(SCE_USER_STYLE_DELIMITER8,	(nestingBuffer+19), 10);	int delim8Nesting		= styler.GetPropertyInt(nestingBuffer, 0);

	commentNesting	|= SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_OPEN
					 | SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_MIDDLE
					 | SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_CLOSE ;

	lineCommentNesting	|= SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_OPEN
						 | SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_MIDDLE
						 | SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_CLOSE ;

	const int backwardsNesting 	= SCE_USER_MASK_NESTING_KEYWORD1
								| SCE_USER_MASK_NESTING_KEYWORD2
								| SCE_USER_MASK_NESTING_KEYWORD3
								| SCE_USER_MASK_NESTING_KEYWORD4
								| SCE_USER_MASK_NESTING_KEYWORD5
								| SCE_USER_MASK_NESTING_KEYWORD6
								| SCE_USER_MASK_NESTING_KEYWORD7
								| SCE_USER_MASK_NESTING_KEYWORD8
								| SCE_USER_MASK_NESTING_OPERATORS2
								| SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_OPEN
								| SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_MIDDLE
								| SCE_USER_MASK_NESTING_FOLDERS_IN_COMMENT_CLOSE
								| SCE_USER_MASK_NESTING_FOLDERS_IN_CODE2_OPEN
								| SCE_USER_MASK_NESTING_FOLDERS_IN_CODE2_MIDDLE
								| SCE_USER_MASK_NESTING_FOLDERS_IN_CODE2_CLOSE ;

	vector<string> & extrasInPrefixedTokens	= (static_cast<Document *>(styler.GetDocumentPointer()))->extrasInPrefixedTokens;
	vector<string> & rangeTokens	        = (static_cast<Document *>(styler.GetDocumentPointer()))->rangeTokens;
	vector<string> & negativePrefixTokens	= (static_cast<Document *>(styler.GetDocumentPointer()))->negativePrefixTokens;
	vector<string> & prefixTokens	        = (static_cast<Document *>(styler.GetDocumentPointer()))->prefixTokens;
	vector<string> & suffixTokens		    = (static_cast<Document *>(styler.GetDocumentPointer()))->suffixTokens;

	vvstring & commentLineOpen 		 = (static_cast<Document *>(styler.GetDocumentPointer()))->commentLineOpen;
	vvstring & commentLineContinue 	 = (static_cast<Document *>(styler.GetDocumentPointer()))->commentLineContinue;
	vvstring & commentLineClose 	 = (static_cast<Document *>(styler.GetDocumentPointer()))->commentLineClose;
	vvstring & commentOpen 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->commentOpen;
	vvstring & commentClose 		 = (static_cast<Document *>(styler.GetDocumentPointer()))->commentClose;
	vvstring & delim1Open 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim1Open;
	vvstring & delim1Escape 		 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim1Escape;
	vvstring & delim1Close 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim1Close;
	vvstring & delim2Open 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim2Open;
	vvstring & delim2Escape 		 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim2Escape;
	vvstring & delim2Close 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim2Close;
	vvstring & delim3Open 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim3Open;
	vvstring & delim3Escape 		 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim3Escape;
	vvstring & delim3Close 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim3Close;
	vvstring & delim4Open 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim4Open;
	vvstring & delim4Escape 		 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim4Escape;
	vvstring & delim4Close 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim4Close;
	vvstring & delim5Open 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim5Open;
	vvstring & delim5Escape 		 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim5Escape;
	vvstring & delim5Close 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim5Close;
	vvstring & delim6Open 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim6Open;
	vvstring & delim6Escape 		 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim6Escape;
	vvstring & delim6Close 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim6Close;
	vvstring & delim7Open 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim7Open;
	vvstring & delim7Escape 		 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim7Escape;
	vvstring & delim7Close 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim7Close;
	vvstring & delim8Open 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim8Open;
	vvstring & delim8Escape 		 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim8Escape;
	vvstring & delim8Close 			 = (static_cast<Document *>(styler.GetDocumentPointer()))->delim8Close;
	vvstring & operators1		  	 = (static_cast<Document *>(styler.GetDocumentPointer()))->operators1;
	// vvstring & operators2		  	 = (static_cast<Document *>(styler.GetDocumentPointer()))->operators2;
	vvstring & foldersInCode1Open	 = (static_cast<Document *>(styler.GetDocumentPointer()))->foldersInCode1Open;
	vvstring & foldersInCode1Middle	 = (static_cast<Document *>(styler.GetDocumentPointer()))->foldersInCode1Middle;
	vvstring & foldersInCode1Close	 = (static_cast<Document *>(styler.GetDocumentPointer()))->foldersInCode1Close;
	//vvstring & foldersInCode2Open	 = (static_cast<Document *>(styler.GetDocumentPointer()))->foldersInCode2Open;
	//vvstring & foldersInCode2Middle	 = (static_cast<Document *>(styler.GetDocumentPointer()))->foldersInCode2Middle;
	//vvstring & foldersInCode2Close	 = (static_cast<Document *>(styler.GetDocumentPointer()))->foldersInCode2Close;

	if (startPos == 0)
	{
		const char * sDelimiters			= styler.pprops->Get("userDefine.delimiters");
		const char * sOperators1			= styler.pprops->Get("userDefine.operators1");
		// const char * sOperators2			= styler.pprops->Get("userDefine.operators2");
		const char * sComments				= styler.pprops->Get("userDefine.comments");

		const char * sFoldersInCode1Open	= styler.pprops->Get("userDefine.foldersInCode1Open");
		const char * sFoldersInCode1Middle	= styler.pprops->Get("userDefine.foldersInCode1Middle");
		const char * sFoldersInCode1Close	= styler.pprops->Get("userDefine.foldersInCode1Close");

		GenerateVector(commentLineOpen,		sComments,   TEXT("00"), 0);
		GenerateVector(commentLineContinue, sComments,   TEXT("01"), commentLineOpen.size());
		GenerateVector(commentLineClose,	sComments,   TEXT("02"), commentLineOpen.size());
		GenerateVector(commentOpen,			sComments,   TEXT("03"), 0);
		GenerateVector(commentClose,		sComments,   TEXT("04"), commentOpen.size());

		GenerateVector(delim1Open,			sDelimiters, TEXT("00"), 0);
		GenerateVector(delim1Escape,		sDelimiters, TEXT("01"), delim1Open.size());
		GenerateVector(delim1Close,		    sDelimiters, TEXT("02"), delim1Open.size());
		GenerateVector(delim2Open,			sDelimiters, TEXT("03"), 0);
		GenerateVector(delim2Escape,		sDelimiters, TEXT("04"), delim2Open.size());
		GenerateVector(delim2Close,		    sDelimiters, TEXT("05"), delim2Open.size());
		GenerateVector(delim3Open,			sDelimiters, TEXT("06"), 0);
		GenerateVector(delim3Escape,		sDelimiters, TEXT("07"), delim3Open.size());
		GenerateVector(delim3Close,		    sDelimiters, TEXT("08"), delim3Open.size());
		GenerateVector(delim4Open,			sDelimiters, TEXT("09"), 0);
		GenerateVector(delim4Escape,		sDelimiters, TEXT("10"), delim4Open.size());
		GenerateVector(delim4Close,		    sDelimiters, TEXT("11"), delim4Open.size());
		GenerateVector(delim5Open,			sDelimiters, TEXT("12"), 0);
		GenerateVector(delim5Escape,		sDelimiters, TEXT("13"), delim5Open.size());
		GenerateVector(delim5Close,		    sDelimiters, TEXT("14"), delim5Open.size());
		GenerateVector(delim6Open,			sDelimiters, TEXT("15"), 0);
		GenerateVector(delim6Escape,		sDelimiters, TEXT("16"), delim6Open.size());
		GenerateVector(delim6Close,		    sDelimiters, TEXT("17"), delim6Open.size());
		GenerateVector(delim7Open,			sDelimiters, TEXT("18"), 0);
		GenerateVector(delim7Escape,		sDelimiters, TEXT("19"), delim7Open.size());
		GenerateVector(delim7Close,		    sDelimiters, TEXT("20"), delim7Open.size());
		GenerateVector(delim8Open,			sDelimiters, TEXT("21"), 0);
		GenerateVector(delim8Escape,		sDelimiters, TEXT("22"), delim8Open.size());
		GenerateVector(delim8Close,		    sDelimiters, TEXT("23"), delim8Open.size());

		operators1.clear();
		// operators2.clear();
		foldersInCode1Open.clear();
		foldersInCode1Middle.clear();
		foldersInCode1Close.clear();

		SubGroup(sOperators1,			operators1,				true);
		// SubGroup(sOperators2,			operators2,				true);
		SubGroup(sFoldersInCode1Open,	foldersInCode1Open,		true);
		SubGroup(sFoldersInCode1Middle,	foldersInCode1Middle,	true);
		SubGroup(sFoldersInCode1Close,	foldersInCode1Close,		true);

		char * numberRanges		    = (char *)styler.pprops->Get("userDefine.numberRanges");
		char * extraCharsInPrefixed	= (char *)styler.pprops->Get("userDefine.extraCharsInPrefixed");
		char * numberPrefixes		= (char *)styler.pprops->Get("userDefine.numberPrefixes");
		char * numberSuffixes		= (char *)styler.pprops->Get("userDefine.numberSuffixes");

		negativePrefixTokens.clear();
		prefixTokens.clear();
		extrasInPrefixedTokens.clear();
		rangeTokens.clear();
		suffixTokens.clear();

		stringToVector(numberPrefixes, prefixTokens);
		stringToVector(numberPrefixes, negativePrefixTokens, true);
		stringToVector(numberSuffixes, suffixTokens);
		stringToVector(extraCharsInPrefixed, extrasInPrefixedTokens);
		stringToVector(numberRanges, rangeTokens);
	}

	vector<forwardStruct> forwards;
	forwards.push_back(*FWS.Set(&delim1Open, 		SCE_USER_STYLE_DELIMITER1, 		SCE_USER_MASK_NESTING_DELIMITER1));
	forwards.push_back(*FWS.Set(&delim2Open, 		SCE_USER_STYLE_DELIMITER2, 		SCE_USER_MASK_NESTING_DELIMITER2));
	forwards.push_back(*FWS.Set(&delim3Open, 		SCE_USER_STYLE_DELIMITER3, 		SCE_USER_MASK_NESTING_DELIMITER3));
	forwards.push_back(*FWS.Set(&delim4Open, 		SCE_USER_STYLE_DELIMITER4, 		SCE_USER_MASK_NESTING_DELIMITER4));
	forwards.push_back(*FWS.Set(&delim5Open, 		SCE_USER_STYLE_DELIMITER5, 		SCE_USER_MASK_NESTING_DELIMITER5));
	forwards.push_back(*FWS.Set(&delim6Open, 		SCE_USER_STYLE_DELIMITER6, 		SCE_USER_MASK_NESTING_DELIMITER6));
	forwards.push_back(*FWS.Set(&delim7Open, 		SCE_USER_STYLE_DELIMITER7, 		SCE_USER_MASK_NESTING_DELIMITER7));
	forwards.push_back(*FWS.Set(&delim8Open, 		SCE_USER_STYLE_DELIMITER8, 		SCE_USER_MASK_NESTING_DELIMITER8));
	forwards.push_back(*FWS.Set(&commentOpen, 		SCE_USER_STYLE_COMMENT, 		SCE_USER_MASK_NESTING_COMMENT));
	forwards.push_back(*FWS.Set(&commentLineOpen, 	SCE_USER_STYLE_COMMENTLINE, 	SCE_USER_MASK_NESTING_COMMENT_LINE));

	vvstring * delimStart[SCE_USER_TOTAL_DELIMITERS];
	delimStart[0] = &delim1Open;
	delimStart[1] = &delim2Open;
	delimStart[2] = &delim3Open;
	delimStart[3] = &delim4Open;
	delimStart[4] = &delim5Open;
	delimStart[5] = &delim6Open;
	delimStart[6] = &delim7Open;
	delimStart[7] = &delim8Open;

	vvstring * multiPartEndVectors[SCE_USER_TOTAL_DELIMITERS + 6];
	multiPartEndVectors[0]  = &operators1;
	multiPartEndVectors[1]  = &commentLineOpen;
	multiPartEndVectors[2]  = &commentLineContinue;
	multiPartEndVectors[3]  = &commentLineClose;
	multiPartEndVectors[4]  = &commentOpen;
	multiPartEndVectors[5]  = &commentClose;
	multiPartEndVectors[6]  = &delim1Close;
	multiPartEndVectors[7]  = &delim2Close;
	multiPartEndVectors[8]  = &delim3Close;
	multiPartEndVectors[9]  = &delim4Close;
	multiPartEndVectors[10] = &delim5Close;
	multiPartEndVectors[11] = &delim6Close;
	multiPartEndVectors[12] = &delim7Close;
	multiPartEndVectors[13] = &delim8Close;
    
	vvstring * delimVectors[SCE_USER_TOTAL_DELIMITERS * 2];
    delimVectors[0]  = &delim1Escape;
    delimVectors[1]  = &delim1Close;
    delimVectors[2]  = &delim2Escape;
    delimVectors[3]  = &delim2Close;
    delimVectors[4]  = &delim3Escape;
    delimVectors[5]  = &delim3Close;
    delimVectors[6]  = &delim4Escape;
    delimVectors[7]  = &delim4Close;
    delimVectors[8]  = &delim5Escape;
    delimVectors[9]  = &delim5Close;
    delimVectors[10] = &delim6Escape;
    delimVectors[11] = &delim6Close;
    delimVectors[12] = &delim7Escape;
    delimVectors[13] = &delim7Close;
    delimVectors[14] = &delim8Escape;
    delimVectors[15] = &delim8Close;
    
    int delimNestings[SCE_USER_TOTAL_DELIMITERS];
    delimNestings[0] = delim1Nesting;
    delimNestings[1] = delim2Nesting;
    delimNestings[2] = delim3Nesting;
    delimNestings[3] = delim4Nesting;
    delimNestings[4] = delim5Nesting;
    delimNestings[5] = delim6Nesting;
    delimNestings[6] = delim7Nesting;
    delimNestings[7] = delim8Nesting;
   
    bool lineContinuation = false;

    bool hasDot = false;
    bool hasExp = false;
	bool hasPrefix = false;

    bool dontMove = false;
    bool finished = true;
    unsigned int nestedLevel = 0;
    int openIndex = 0;
    int skipForward = 0;
	int prevState = 0;

    int isCommentLine = COMMENTLINE_NO;
    int isPrevLineComment = COMMENTLINE_NO;
	bool isInCommentBlock = false;
    bool isInComment = false;
    unsigned int commentBlockStart = static_cast<unsigned int>(-1);
    unsigned int commentBlockEnd = 0;
	bool setFoldEndAtEOL = false;
	int oldStartPos = startPos;
    int newState = 0;

	vector<nestedInfo> lastNestedGroup;

	vvstring * delimEscape = NULL;
	vvstring * delimClose  = NULL;
	int delimNesting = 0;
    int foldInComment = FOLD_NONE;

	if (startPos == 0)
	{
		foldVector.clear();
		nestedVector.clear();
		lastNestedGroup.clear();
		initStyle = SCE_USER_STYLE_DEFAULT;
	}
	else
	{
		ReColoringCheck( startPos, initStyle, nestedLevel, openIndex, isPrevLineComment, isInCommentBlock,
						 commentBlockStart, setFoldEndAtEOL, styler, isInComment, isCommentLine, lastNestedGroup);

		// offset move to previous line
		length += (oldStartPos - startPos);
	}

    StyleContext sc(startPos, length, initStyle, styler);
    for (; finished; dontMove?true:sc.Forward())
    {
        dontMove = false;
        if (sc.More() == false)
        {
            finished = false;   // colorize last word, even if file does not end with whitespace char
        }

        if (foldComments)
			if (!isInComment)
				if (isCommentLine == COMMENTLINE_NO)
					if (!isWhiteSpace(sc.ch))
						if (sc.state != SCE_USER_STYLE_COMMENTLINE)
							if (sc.state != SCE_USER_STYLE_DEFAULT)
								if (sc.state != SCE_USER_STYLE_IDENTIFIER)
									isCommentLine = COMMENTLINE_SKIP_TESTING;

		if (sc.atLineEnd)
		{
			CommentBlockCheck(isPrevLineComment, isCommentLine, isInCommentBlock, commentBlockStart,
							  commentBlockEnd, sc, isInComment, setFoldEndAtEOL, foldInComment);
	    }

        switch (sc.state)
        {
            case SCE_USER_STYLE_NUMBER :
            {
                if (sc.ch == '.')
                {
                    if (hasDot || !IsADigit(sc.chNext) || (sc.chNext == 'e' || sc.chNext == 'E'))
                    {
                        sc.SetState(SCE_USER_STYLE_DEFAULT);
                        dontMove = false;
                        hasDot = false;
                        hasExp = false;
						hasPrefix = false;
                        break;
                    }
                    sc.Forward();
                    hasDot = true;
                }
                if (sc.ch == 'e' || sc.ch == 'E')
                {
                    if (!hasExp)
                    {
                        if (IsADigit(sc.chNext) || sc.chNext == '+' || sc.chNext == '-')
                        {
                            sc.Forward();
                            hasExp = true;
							hasDot = false;
							hasPrefix = false;
							break;
                        }
                    }
                    else
                    {
                        sc.SetState(SCE_USER_STYLE_DEFAULT);
                        dontMove = false;
                        hasDot = false;
                        hasExp = false;
						hasPrefix = false;
                        break;
                    }
                }

				int test = isADigit(sc, ignoreCase, rangeTokens, hasPrefix, extrasInPrefixedTokens);

				if (test == NUMBER_RANGE_CHAR && !IsADigit(sc.chNext))
				{
                    sc.SetState(SCE_USER_STYLE_DEFAULT);
                    dontMove = true;
                    hasDot = false;
                    hasExp = false;
					hasPrefix = false;
                    break;
				}

                if (test == NUMBER_NOT_A_NUMBER)
                {
                    vector<string>::iterator iter = suffixTokens.begin();
                    for (; iter != suffixTokens.end(); ++iter)
                    {
                        if (ignoreCase)
                        {
                            if (sc.MatchIgnoreCase(iter->c_str()))
                                break;
                        }
                        else if (sc.Match(iter->c_str()))
                            break;
                    }
                    if (iter != suffixTokens.end())
                        sc.Forward(iter->length());

                    sc.SetState(SCE_USER_STYLE_DEFAULT);
                    dontMove = true;
                    hasDot = false;
                    hasExp = false;
					hasPrefix = false;
                    break;
                }
                break;
            }

            case SCE_USER_STYLE_DELIMITER1 :
			case SCE_USER_STYLE_DELIMITER2 :
			case SCE_USER_STYLE_DELIMITER3 :
			case SCE_USER_STYLE_DELIMITER4 :
			case SCE_USER_STYLE_DELIMITER5 :
			case SCE_USER_STYLE_DELIMITER6 :
			case SCE_USER_STYLE_DELIMITER7 :
			case SCE_USER_STYLE_DELIMITER8 :
            {
                int index	= sc.state - SCE_USER_STYLE_DELIMITER1;
                delimEscape = delimVectors[index*2];
                delimClose	= delimVectors[index*2 + 1];
                delimNesting = delimNestings[index];
  				prevState = sc.state;
  				newState  = sc.state;
                
                // first, check escape sequence
                vector<string>::iterator iter = (*delimEscape)[openIndex].begin();
                for (; iter != (*delimEscape)[openIndex].end(); ++iter)
                {
                    if (ignoreCase?sc.MatchIgnoreCase(iter->c_str()):sc.Match(iter->c_str()))
                    {
                        sc.Forward(iter->length() + 1); // escape is found, skip escape string and one char after it.
                        break;
                    }
                }

                // second, check end of delimiter sequence
                iter = (*delimClose)[openIndex].begin();
                for (; iter != (*delimClose)[openIndex].end(); ++iter)
                {
                    if (ignoreCase?sc.MatchIgnoreCase(iter->c_str()):sc.Match(iter->c_str()))
                    {
                        nestedVector.push_back(*NI.Set(sc.currentPos + iter->length() - 1, nestedLevel--, openIndex, sc.state, NI_CLOSE));

						setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, delimNesting, multiPartEndVectors);
                        sc.SetState(sc.state);
                        readLastNested(lastNestedGroup, newState, openIndex);
						if (newState != SCE_USER_STYLE_COMMENTLINE || (sc.ch != '\r' && sc.ch != '\n')) // for delimiters that end with ((EOL))
							sc.Forward(iter->length());

                        sc.SetState(newState);

                        dontMove = true;
                        break; // get out of 'for', not 'case'
                    }
                }

				if (prevState != newState)  // out of current state?
					break;  

                if (isWhiteSpace(sc.ch) && !isWhiteSpace(sc.chPrev))    // quick replacement for SCE_USER_STYLE_IDENTIFIER
                {
                    setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, delimNesting, multiPartEndVectors);
                    sc.SetState(sc.state);
                }
                else if (!isWhiteSpace(sc.ch) && isWhiteSpace(sc.chPrev))   // create new 'compare point'
                {
                    sc.SetState(sc.state);
                }

                // third, check nested delimiter sequence
                if (isInListNested(delimNesting, forwards, sc, ignoreCase, openIndex, skipForward, newState))
				{
                    setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, delimNesting, multiPartEndVectors);

                    nestedVector.push_back(*NI.Set(sc.currentPos, ++nestedLevel, openIndex, newState, NI_OPEN));
                    lastNestedGroup.push_back(NI);

                    sc.SetState(newState);
                    sc.Forward(skipForward);
                    sc.SetState(newState);
                    dontMove = true;
                    break;
				}
                break;
            }

            case SCE_USER_STYLE_COMMENT :
            {
                // first, check end of comment sequence
                vector<string>::iterator iter = commentClose[openIndex].begin();
                for (; iter != commentClose[openIndex].end(); ++iter)
                {
                    if (ignoreCase?sc.MatchIgnoreCase(iter->c_str()):sc.Match(iter->c_str()))
                    {
                        nestedVector.push_back(*NI.Set(sc.currentPos + iter->length() - 1, nestedLevel--, openIndex, SCE_USER_STYLE_COMMENT, NI_CLOSE));

						setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, commentNesting, multiPartEndVectors);
						sc.SetState(SCE_USER_STYLE_COMMENT);
                        sc.Forward(iter->length());

						readLastNested(lastNestedGroup, newState, openIndex);
                        sc.SetState(newState);

                        if (foldComments)
							setFoldEndAtEOL = true;
                        isInComment = false;

                        dontMove = true;
                        break;
                    }
                }

				if (sc.state != SCE_USER_STYLE_COMMENT)
					break;

                if (isWhiteSpace(sc.ch) && !isWhiteSpace(sc.chPrev))    // quick replacement for SCE_USER_STYLE_IDENTIFIER
                {
                    setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, commentNesting, multiPartEndVectors);
                    sc.SetState(SCE_USER_STYLE_COMMENT);
                }
                else if (!isWhiteSpace(sc.ch) && isWhiteSpace(sc.chPrev))   // create new 'compare point'
                {
                    sc.SetState(SCE_USER_STYLE_COMMENT);
                }

                // second, update comment folding variables
                if (foldComments && sc.atLineStart && !isInCommentBlock && commentBlockStart == -1)
                {
                    commentBlockStart = sc.currentPos;
                }

                if (foldComments && sc.atLineEnd && isInCommentBlock)
                {
                    commentBlockEnd = sc.currentPos;
				}

                // third, check nested delimiter sequence
                if (isInListNested(commentNesting, forwards, sc, ignoreCase, openIndex, skipForward, newState))
				{
                    setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, commentNesting, multiPartEndVectors);

                    nestedVector.push_back(*NI.Set(sc.currentPos, ++nestedLevel, openIndex, newState, NI_OPEN));
                    lastNestedGroup.push_back(NI);

                    sc.SetState(newState);
                    sc.Forward(skipForward);
                    sc.SetState(newState);
                    dontMove = true;
                    break;
				}
                break;
            }

            case SCE_USER_STYLE_COMMENTLINE :
            {
				// first, check end of line comment sequence (in rare cases when line comments can end before new line char)
                vector<string>::iterator iter = commentLineClose[openIndex].begin();
                for (; iter != commentLineClose[openIndex].end(); ++iter)
                {
                    if (ignoreCase?sc.MatchIgnoreCase(iter->c_str()):sc.Match(iter->c_str()))
                    {
                        nestedVector.push_back(*NI.Set(sc.currentPos + iter->length() - 1, nestedLevel--, openIndex, SCE_USER_STYLE_COMMENTLINE, NI_CLOSE));

						setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, lineCommentNesting, multiPartEndVectors);
						sc.SetState(SCE_USER_STYLE_COMMENTLINE);
						sc.Forward(iter->length());
                        readLastNested(lastNestedGroup, newState, openIndex);
                        sc.SetState(newState);

                        if (foldComments)
                            setFoldEndAtEOL = true;

                        dontMove = true;
                        break;
                    }
                }

				if (sc.state != SCE_USER_STYLE_COMMENTLINE)
					break;

                if (isWhiteSpace(sc.ch) && !isWhiteSpace(sc.chPrev))    // quick replacement for SCE_USER_STYLE_IDENTIFIER
                {
                    setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, lineCommentNesting, multiPartEndVectors);
                    sc.SetState(SCE_USER_STYLE_COMMENTLINE);
                }
                else if (!isWhiteSpace(sc.ch) && isWhiteSpace(sc.chPrev))   // create new 'compare point'
                {
                    sc.SetState(SCE_USER_STYLE_COMMENTLINE);
                }

                // second, check line comment continuation
                if (sc.atLineEnd)
                {
					// in case line comments support line continuation
					lineContinuation = CheckLineContinuation(commentLineContinue, styler, openIndex, sc.currentPos, ignoreCase);
                    //{ int offset = 0;
                    // if (sc.chPrev == '\r')
                        // offset = 1;

                    // lineContinuation = false;
                    // vector<string>::iterator iter = commentLineContinue[openIndex].begin();
                    // for (; iter != commentLineContinue[openIndex].end(); ++iter)
                    // {
                        // int length = iter->length();
                        // if (length == 0)
                            // continue;

						// lineContinuation = true;
                        // for (int i=0; i<length; ++i)
                        // {
                            // if (ignoreCase)
                            // {
                                // if (toupper((*iter)[i]) != toupper(styler.SafeGetCharAt(sc.currentPos - length + i - offset, 0)))
                                // {
                                    // lineContinuation = false;
                                    // break;
                                // }
                            // }
                            // else if ((*iter)[i] != styler.SafeGetCharAt(sc.currentPos - length + i - offset, 0))
                            // {
                                // lineContinuation = false;
                                // break;
                            // }
                        // }
                        // if (lineContinuation)
                            // break;
                    //}

					sc.Forward();   // set state of '\n'
                    sc.ChangeState(SCE_USER_STYLE_COMMENTLINE);
                    if (!lineContinuation)
                    {
                        nestedVector.push_back(*NI.Set(sc.currentPos - 1, nestedLevel--, openIndex, SCE_USER_STYLE_COMMENTLINE, NI_CLOSE));

	                    sc.ChangeState(SCE_USER_STYLE_COMMENTLINE);
                        readLastNested(lastNestedGroup, newState, openIndex);
                        sc.SetState(newState);
                    }

                    dontMove = true;
                    lineContinuation = false;
                    break;
                }

				if (sc.state != SCE_USER_STYLE_COMMENTLINE)
					break;

                // third, check nested delimiter sequence
                if (isInListNested(lineCommentNesting, forwards, sc, ignoreCase, openIndex, skipForward, newState))
				{
                    setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, lineCommentNesting, multiPartEndVectors);

                    nestedVector.push_back(*NI.Set(sc.currentPos, ++nestedLevel, openIndex, newState, NI_OPEN));
                    lastNestedGroup.push_back(NI);

                    sc.SetState(newState);
                    sc.Forward(skipForward);
                    sc.SetState(newState);
                    dontMove = true;
                    break;
				}

                break;
            }

            case SCE_USER_STYLE_IDENTIFIER :
            {
                if (isWhiteSpace(sc.ch))
                {
                    setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, backwardsNesting, multiPartEndVectors);
                    sc.SetState(SCE_USER_STYLE_DEFAULT);
                    break;
                }

				if (!commentLineOpen.empty())
                {
                    if (isInList2(commentLineOpen, sc, ignoreCase, openIndex, skipForward))
                    {
                        if (foldComments && isCommentLine != COMMENTLINE_SKIP_TESTING)
                        {
                            isCommentLine = COMMENTLINE_YES;
							if (isPrevLineComment)
								setFoldEndAtEOL = true;
                            if (commentBlockStart == -1)
                                commentBlockStart = sc.currentPos;
                        }

                        setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, backwardsNesting, multiPartEndVectors);
						sc.SetState(SCE_USER_STYLE_COMMENTLINE);

						nestedVector.push_back(*NI.Set(sc.currentPos, ++nestedLevel, openIndex, SCE_USER_STYLE_COMMENTLINE, NI_OPEN));
						lastNestedGroup.push_back(NI);

						sc.Forward(skipForward);
						sc.SetState(SCE_USER_STYLE_COMMENTLINE);
                        dontMove = true;
                        break;
                    }
				}

				if (!commentOpen.empty())
                {
                    if (isInList2(commentOpen, sc, ignoreCase, openIndex, skipForward))
                    {
						if (isCommentLine != COMMENTLINE_SKIP_TESTING)
						{
							isCommentLine = COMMENTLINE_YES;
							if (foldComments)
							{
								if (commentBlockStart == -1)
									commentBlockStart = sc.currentPos;
							}
						}

                        setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, backwardsNesting, multiPartEndVectors);
                        sc.SetState(SCE_USER_STYLE_COMMENT);

						nestedVector.push_back(*NI.Set(sc.currentPos, ++nestedLevel, openIndex, SCE_USER_STYLE_COMMENT, NI_OPEN));
						lastNestedGroup.push_back(NI);

                        sc.Forward(skipForward);
						sc.SetState(SCE_USER_STYLE_COMMENT);
                        dontMove = true;
						isInComment = true;
                        break;
                    }
                }

				for (int i=0; i<SCE_USER_TOTAL_DELIMITERS; ++i)
				{
					if (!delimStart[i]->empty())
					{
						if (isInList2(*delimStart[i], sc, ignoreCase, openIndex, skipForward))
						{
							setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, backwardsNesting, multiPartEndVectors);
							sc.SetState(i+SCE_USER_STYLE_DELIMITER1);
							nestedVector.push_back(*NI.Set(sc.currentPos, ++nestedLevel, openIndex, i+SCE_USER_STYLE_DELIMITER1, NI_OPEN));
							lastNestedGroup.push_back(NI);
							sc.Forward(skipForward);
							sc.SetState(i+SCE_USER_STYLE_DELIMITER1);
							dontMove = true;
							break;	// break from nested for loop
						}
					}
				}
				if (dontMove == true)
					break;	// delimiter start found, break from case SCE_USER_STYLE_IDENTIFIER

				if (!operators1.empty())
                {
					if (isInList2(operators1, sc, ignoreCase, openIndex, skipForward))
					{
                        setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, backwardsNesting, multiPartEndVectors);
                        sc.SetState(SCE_USER_STYLE_OPERATOR);
						sc.Forward(skipForward);
						sc.ChangeState(SCE_USER_STYLE_OPERATOR);
						sc.SetState(SCE_USER_STYLE_DEFAULT);
                        dontMove = true;
                        break;
					}
                }
                
				if (!foldersInCode1Open.empty())
                {
					if (isInList2(foldersInCode1Open, sc, ignoreCase, openIndex, skipForward))
					{
                        setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, backwardsNesting, multiPartEndVectors);
						sc.SetState(SCE_USER_STYLE_FOLDER_IN_CODE1);
						sc.Forward(skipForward);
						sc.ChangeState(SCE_USER_STYLE_FOLDER_IN_CODE1);
						sc.SetState(SCE_USER_STYLE_DEFAULT);
                        dontMove = true;

						if (foldInComment == FOLD_CLOSE)
							foldInComment = FOLD_MIDDLE;
						else if (foldInComment == FOLD_NONE)
							foldInComment = FOLD_OPEN;
						else
							foldInComment = FOLD_NONE;

                        break;
					}
                }

				if (!foldersInCode1Middle.empty())
                {
					if (isInList2(foldersInCode1Middle, sc, ignoreCase, openIndex, skipForward))
					{
                        setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, backwardsNesting, multiPartEndVectors);
						sc.SetState(SCE_USER_STYLE_FOLDER_IN_CODE1);
						sc.Forward(skipForward);
						sc.ChangeState(SCE_USER_STYLE_FOLDER_IN_CODE1);
						sc.SetState(SCE_USER_STYLE_DEFAULT);
                        dontMove = true;

						if (foldInComment == FOLD_NONE)
							foldInComment = FOLD_MIDDLE;
						else
							foldInComment = FOLD_NONE;

                        break;
					}
                }

				if (!foldersInCode1Close.empty())
                {
					if (isInList2(foldersInCode1Close, sc, ignoreCase, openIndex, skipForward))
					{
                        setBackwards(keywordlists, sc, prefixes, ignoreCase, foldInComment, backwardsNesting, multiPartEndVectors);
						sc.SetState(SCE_USER_STYLE_FOLDER_IN_CODE1);
						sc.Forward(skipForward);
						sc.ChangeState(SCE_USER_STYLE_FOLDER_IN_CODE1);
						sc.SetState(SCE_USER_STYLE_DEFAULT);
                        dontMove = true;

						if (foldInComment == FOLD_NONE || foldInComment == FOLD_MIDDLE)
							foldInComment = FOLD_CLOSE;
						else
							foldInComment = FOLD_NONE;

                        break;
					}
                }

                if (isCommentLine != COMMENTLINE_SKIP_TESTING)
                    isCommentLine = COMMENTLINE_SKIP_TESTING;

                break;
            }

            // determine if a new state should be entered.
            case SCE_USER_STYLE_DEFAULT :
            {
				if (isWhiteSpace(sc.ch))// && isWhiteSpace(sc.chPrev))
                {
                    break;
                }

				// does a number prefix start here?
				vector<string>::iterator iter = prefixTokens.begin();
				vector<string>::iterator last = prefixTokens.end();
				if (sc.ch == '-')
				{
					iter = negativePrefixTokens.begin();
					last = negativePrefixTokens.end();
				}
				for (; iter != last; ++iter)
				{
					if (ignoreCase ? sc.MatchIgnoreCase(iter->c_str()) : sc.Match(iter->c_str()))
                        break;
				}
				if (iter != last)
				{
					sc.SetState(SCE_USER_STYLE_NUMBER);
					sc.Forward(iter->length());
					hasPrefix = true;
					dontMove = true;
					break;
				}

                if (IsADigit(sc.ch) || (sc.ch == '-' && IsADigit(sc.chNext)))
                {
                    sc.SetState(SCE_USER_STYLE_NUMBER);
                    break;
                }
                else if (sc.ch == '.' && IsADigit(sc.chNext))
                {
                    hasDot = true;
                    sc.SetState(SCE_USER_STYLE_NUMBER);
                    break;
                }

                if (!isWhiteSpace(sc.ch))// && isWhiteSpace(sc.chPrev)) // word start
                {
                    sc.SetState(SCE_USER_STYLE_IDENTIFIER);
                    dontMove = true;
                    break;
                }
                break;
            }

            default :
                break;
        }

    }
    sc.Complete();
}

static void FoldUserDoc(unsigned int startPos, int length, int /*initStyle*/, WordList *[],  Accessor &styler)
{
    int lineCurrent = styler.GetLine(startPos);
    int linePrev = lineCurrent;
	int levelCurrent = SC_FOLDLEVELBASE;

	if (lineCurrent > 0)
	{
		//	//levelCurrent = styler.LevelAt(lineCurrent) >> 16;
		//	//linePrev = lineCurrent - 1;
		//	//levelPrev = styler.LevelAt(linePrev) & SC_FOLDLEVELNUMBERMASK;
		//	levelCurrent = styler.LevelAt(lineCurrent) & SC_FOLDLEVELNUMBERMASK;
		levelCurrent = styler.LevelAt(lineCurrent) & SC_FOLDLEVELNUMBERMASK;
	}
	int levelPrev = levelCurrent;

    vector<foldInfo>::iterator iter = foldVector.begin();

	int test = 0;
	for (int i=0; i<9; ++i)
	{
		test = styler.LevelAt(i);
	}

	if (lineCurrent > 0)
	{
		for (; iter != foldVector.end(); ++iter)
		{
			//if (styler.GetLine(iter->position) == linePrev)
			//{
			//	if (iter->state == FOLD_CLOSE)
			//		--levelPrev;
			//}
			//int d = styler.GetLine(iter->position);
			if (styler.GetLine(iter->position) == lineCurrent)
			{
				//if (iter->state == FOLD_OPEN)
				//{
				//	levelCurrent = styler.LevelAt(lineCurrent) & SC_FOLDLEVELNUMBERMASK;
				//	levelPrev = levelCurrent;
				//}

				if (iter->state == FOLD_MIDDLE)
				{
					levelCurrent = (styler.LevelAt(lineCurrent) >> 16) & SC_FOLDLEVELNUMBERMASK;
					levelPrev = (styler.LevelAt(lineCurrent)) & SC_FOLDLEVELNUMBERMASK;
					++levelPrev;
				}
				if (iter->state == FOLD_CLOSE)
				{
					levelCurrent = styler.LevelAt(lineCurrent);
					levelPrev = levelCurrent - 1;
					//--levelCurrent;
				}
			}
			if (styler.GetLine(iter->position) >= lineCurrent)
				break;
		}
	}

    for (; iter != foldVector.end(); ++iter)
    {
        lineCurrent = styler.GetLine(iter->position);
        for (int line=linePrev+1; line<lineCurrent; ++line)
            styler.SetLevel(line, levelPrev);

        if (iter->state == FOLD_OPEN)
        {
            levelCurrent++;
            styler.SetLevel(lineCurrent, levelPrev | SC_FOLDLEVELHEADERFLAG);
        }
        else if (iter->state == FOLD_MIDDLE)
        {
			int lev = ((levelPrev-1) | (levelCurrent << 16)) | SC_FOLDLEVELHEADERFLAG;
            styler.SetLevel(lineCurrent, lev);
        }
        else if (iter->state == FOLD_CLOSE)
        {
            styler.SetLevel(lineCurrent, levelCurrent);
            levelCurrent--;
        }

        levelPrev = levelCurrent;
		linePrev = lineCurrent;
    }

    // Fill in the real level of the next line, keeping the current flags as they will be filled in later
	int lastLine = styler.GetLine(startPos + length);

    for (int line=linePrev+1; line<=lastLine; ++line)
       styler.SetLevel(line, levelPrev);

	if (lineCurrent != lastLine)
	{
		int flagsNext = styler.LevelAt(lastLine) & ~SC_FOLDLEVELNUMBERMASK;
		styler.SetLevel(lastLine, levelPrev | flagsNext);
	}

}

static const char * const userDefineWordLists[] = {
            "Primary keywords and identifiers",
            "Secondary keywords and identifiers",
            "Documentation comment keywords",
            "Fold header keywords",
            0,
        };

LexerModule lmUserDefine(SCLEX_USER, ColouriseUserDoc, "user", FoldUserDoc, userDefineWordLists);
