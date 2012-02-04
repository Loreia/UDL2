/*
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
*/

#ifndef URLCTRL_INCLUDED
#define URLCTRL_INCLUDED

class URLCtrl : public Window {
public:
    URLCtrl():_hfUnderlined(0),_hCursor(0), _msgDest(NULL), _cmdID(0), _oldproc(NULL), \
		_linkColor(), _visitedColor(), _clicking(false), _URL(TEXT("")){};

    void create(HWND itemHandle, TCHAR * link, COLORREF linkColor = RGB(0,0,255));
	void create(HWND itemHandle, int cmd, HWND msgDest = NULL);
    void destroy();

protected :
    generic_string _URL;
    HFONT	_hfUnderlined;
    HCURSOR	_hCursor;

	HWND _msgDest;
	unsigned long _cmdID;

    WNDPROC  _oldproc;
    COLORREF _linkColor;			
    COLORREF _visitedColor;
    bool  _clicking;

    static LRESULT CALLBACK URLCtrlProc(HWND hwnd, UINT Message, WPARAM wParam, LPARAM lParam){
        return ((URLCtrl *)(::GetWindowLongPtr(hwnd, GWL_USERDATA)))->runProc(hwnd, Message, wParam, lParam);
    };
    LRESULT runProc(HWND hwnd, UINT Message, WPARAM wParam, LPARAM lParam);
};

#endif //URLCTRL_INCLUDED
